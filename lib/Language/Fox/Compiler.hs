{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Fox.Compiler ( compiler, compile ) where

import           Data.Monoid
import           Control.Arrow                    ((>>>))
import           Prelude                  hiding (compare)
import           Control.Monad                   (void)
import           Data.Maybe
import           Data.Bits                       (shift)
import           Language.Fox.Types
import           Language.Fox.Parser     (parse)
import           Language.Fox.Checker    (check, errUnboundVar)
import           Language.Fox.Normalizer (anormal)
import           Language.Fox.Asm        (asm)
import           Language.Fox.Label


--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> tails >>> compile >>> asm


--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Ann@
--------------------------------------------------------------------------------
type Ann   = ((SourceSpan, Int), Bool)
type AExp  = AnfExpr Ann
type IExp  = ImmExpr Ann
type ABind = Bind    Ann
type ADcl  = Decl    Ann
type APgm  = Program Ann

instance Located Ann where
  sourceSpan = fst . fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

annTag :: Ann -> Int
annTag = snd . fst

annTail :: Ann -> Bool
annTail = snd


--------------------------------------------------------------------------------
compile :: APgm -> [Instruction]
--------------------------------------------------------------------------------
compile (Prog ds e) = compileBody emptyEnv e
                   ++ concatMap compileDecl ds

compileDecl :: ADcl -> [Instruction]
compileDecl (Decl f xs e _) = ILabel (DefFun (bindId f))
                            : compileBody env e
  where
    env                     = fromListEnv (zip (bindId <$> xs) [-2, -3..])

compileBody :: Env -> AExp -> [Instruction]
compileBody env e = funInstrs (countVars e) (compileEnv env e)

-- | @funInstrs n body@ returns the instructions of `body` wrapped
--   with code that sets up the stack (by allocating space for n local vars)
--   and restores the callees stack prior to return - 

funInstrs :: Int -> [Instruction] -> [Instruction]
funInstrs n instrs
  = funEntry n
 ++ instrs
 ++ funExit
 ++ [IRet]

-- instructions for setting up stack for `n` local vars
funEntry :: Int -> [Instruction]
funEntry n = [ IPush (Reg EBP)                       -- save caller's ebp
             , IMov  (Reg EBP) (Reg ESP)             -- set callee's ebp
             , ISub  (Reg ESP) (Const (4 * n))       -- allocate n local-vars
             ]
          ++ [ clearStackVar i | i <- [1..n] ]       -- zero out stack-vars

-- clean up stack & labels for jumping to error
funExit :: [Instruction]
funExit   = [ IMov (Reg ESP) (Reg EBP)          -- restore callee's esp
            , IPop (Reg EBP)                    -- restore callee's ebp
            ]

clearStackVar :: Int -> Instruction
clearStackVar i = IMov (Sized DWordPtr (stackVar i)) (Const 0)

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e)  (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@Number {}       = [ compileImm env v  ]

compileEnv env v@Boolean {}      = [ compileImm env v  ]

compileEnv env v@Id {}           = [ compileImm env v  ]

compileEnv env e@(Let x e1 e2 _) = is ++ compileEnv env' body ++ [clearStackVar $ fromMaybe err (lookupEnv (bindId x) env')] ++ clearBinds
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e
    clearBinds                   = [clearStackVar $ fromMaybe err (lookupEnv (bindId ( fst x')) env') | x' <-binds] 
    err                          = abort (errUnboundVar (sourceSpan e) $ bindId x)

--binds = [(Bind a, Expr a)]

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env v@(Tuple expr l)    = compileTuple l env v  

compileEnv env v@(GetItem e1 e2 l) = compileGet l env v 

compileEnv env (If v e1 e2 l)    = compileIf l env v e1 e2

compileEnv env (App fname vs l)
  | annTail l =
    ISub (Reg ESP) (Const $ 4 * length vs) :
    concat [ [ IMov (Reg EAX) (Sized DWordPtr (funArg i))
             , IMov (Sized DWordPtr (stackVar (n+i))) (Reg EAX)
             ]
           | i <- [1..(length vs)]
           ]
    ++ tailcall (DefFun fname) tailArgs

  | otherwise = call (DefFun fname) args
  where
    funArg i = stackVar (-1 * (i+1))
    n        = envMax env
    args     = param env <$> vs
    tailArgs = f <$> args

    f a@(Sized DWordPtr (RegOffset i4 EBP))
      | i4 >= 8   = let i  = (i4 `div` 4) - 1
                    in Sized DWordPtr (stackVar (i + n))
      | otherwise = a
    f a = a

    tailcall :: Label -> [Arg] -> [Instruction]
    tailcall f2 args2 = copyArgs args2 ++ funExit ++ [IJmp f2]

    copyArgs :: [Arg] -> [Instruction]
    copyArgs = concat . zipWith copyArg [-2, -3..]
      where
        copyArg i a = [ IMov (Reg EAX) a
                      , IMov (stackVar i) (Reg EAX)
                      ]

compileBind :: Env -> (ABind, AExp) -> (Env, Int, [Instruction])
compileBind env (x, e) = (env', xi, is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar xi) (Reg EAX)]
    (xi, env')         = pushEnv x env

compilePrim1 :: Ann -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1    v = compilePrim2 l env Plus  v (Number 1 l)
compilePrim1 l env Sub1    v = compilePrim2 l env Minus v (Number 1 l)
compilePrim1 l env IsNum   v = isType l env v TNumber
compilePrim1 l env IsBool  v = isType l env v TBoolean
compilePrim1 l env IsTuple v = isType l env v TTuple
compilePrim1 _ env Print   v = call (Builtin "print") [param env v]

compilePrim2 :: Ann -> Env -> Prim2 -> IExp -> IExp -> [Instruction]

compilePrim2 l env Plus  v1 v2 =  assertType env v1 TNumber
                                  ++ assertType env v2 TNumber
                                  ++ [ IMov (Reg EAX) (immArg env v1)
                                  , IAdd (Reg EAX) (immArg env v2)
                                  , IJo (DynamicErr ArithOverflow)
                                  ] 

compilePrim2 l env Minus v1 v2 =  assertType env v1 TNumber
                                  ++ assertType env v2 TNumber
                                  ++ [IMov (Reg EAX) (immArg env v1)
                                     ,ISub (Reg EAX) (immArg env v2)
                                     , IJo (DynamicErr ArithOverflow)
                                     ]
compilePrim2 l env Times v1 v2 =  assertType env v1 TNumber
                                  ++ assertType env v2 TNumber ++ 
                                  [ IMov (Reg EAX) (immArg env v1)
                                  , IMul (Reg EAX) (immArg env v2)
                                  , IJo (DynamicErr ArithOverflow)
                                  , ISar (Reg EAX) (Const 1)
                                  ]
compilePrim2 l env Less    v1 v2 =   assertType env v1 TNumber 
                                  ++ assertType env v2 TNumber
                                  ++ [ IMov (Reg EAX) (immArg env v1)
                                     , ISub (Reg EAX) (immArg env v2)
                                     , IAnd (Reg EAX) (HexConst 0x80000000)
                                     , IOr  (Reg EAX) (HexConst 0x7fffffff)
                                  ]

compilePrim2 l env Greater v1 v2 =   assertType env v1 TNumber
                                  ++ assertType env v2 TNumber
                                  ++ [ IMov (Reg EAX) (immArg env v2)
                                     , ISub (Reg EAX) (immArg env v1)
                                     , IAnd (Reg EAX) (HexConst 0x80000000)
                                     , IOr  (Reg EAX) (HexConst 0x7fffffff)
                                  ]

compilePrim2 l env Equal   v1 v2 =  [
                                        IMov (Reg EAX) (immArg env v2)
                                      , ISub (Reg EAX) (immArg env v1)
                                      , ICmp (Reg EAX) (HexConst 0x000000000) 
                                      , IJe $BranchTrue $annTag l
                                      , IMov (Reg EAX) (repr False)
                                      , IJmp $BranchDone $annTag l
                                      , ILabel $BranchTrue $annTag l
                                      , IMov (Reg EAX) (repr True)
                                      , ILabel $BranchDone $annTag l
                                    ]

compileIf :: Ann -> Env -> IExp -> AExp -> AExp -> [Instruction]
compileIf l env v e1 e2 =
                            (compileEnv env v)
                          ++ assertType env v TBoolean
                          ++ [ICmp (Reg EAX) (repr False)] 
                          ++ [IJe $BranchTrue $annTag l]
                          ++ (compileEnv env e1)
                          ++ [IJmp $BranchDone $annTag l]
                          ++ [ILabel $BranchTrue $annTag l]
                          ++ (compileEnv env e2)
                          ++ [ILabel $BranchDone $annTag l]

compileGet :: Ann -> Env -> AExp -> [Instruction]  
compileGet l env (GetItem e1 e2 ls)  
                                =  assertType env e1 TTuple             -- assert Tag bits set
                                ++ assertType env e2 TNumber
                                ++ [ IMov (Reg EAX) (immArg env e1) ]   -- put pointer in EAX
                                ++ unsetTag EAX TTuple                  -- get EAX address
                                ++ [IMov (Reg EBX) (immArg env e2)]     -- Get index
                                ++ checkIndexBounds 
                                ++ [ISar (Reg EBX) (Const 1)
                                , IAdd (Reg EAX) (Const 8)
                                , IMov (Reg EAX) (RegIndex (EAX) (EBX))]-- get address of element
compileTuple :: Ann -> Env -> AExp -> [Instruction]
compileTuple l env x@(Tuple expr ls) =
                                 tupleReserve l ((numWords + padding) * 4 ) 
                               ++ [IMov (Reg EAX) (Reg ESI)]      -- Put pointer into EAX
                               ++ setTag (EAX)(TTuple)         -- Set tag for pointer
                               ++ setMetaData x                 -- Add metadata how many elements
                               ++ valueCopy 8 env expr         -- Puts list elements onto heap
                               ++ [IAdd (Reg ESI) (Const $ 8 + 4 * length expr)] -- Update ESI
                               ++ addPadding (length expr)     -- Adds padding to ESI if needed
                                where 
                                  numWords = length expr + 2 
                                  padding  = if (odd numWords) then 1 else 0 
--Assumptions EBX contains index & ESI points to length
checkIndexBounds :: [Instruction]
checkIndexBounds = [ICmp (Reg EBX) (Const 0)            --Check index > 0 
                    ,IJl (DynamicErr IndexLow)          --
                    ,ICmp (Reg EBX) (RegOffset 0 EAX )  --Check index < length
                    ,IJge  (DynamicErr IndexHigh)]

addPadding :: Int -> [Instruction]
addPadding x = if (odd x )
                     then [IAdd (Reg ESI) (Const 4)] 
                     else [] 
valueCopy :: Int -> Env -> [AExp] -> [Instruction]
valueCopy index env []      = []
valueCopy index env (x:xs) 
 = 
   [ IMov (Reg EBX) (immArg env x)
   , IMov (RegOffset index ESI) (Reg EBX)
   ] 
   ++ valueCopy (index+4) env xs

setMetaData :: AExp -> [Instruction]
setMetaData (Tuple expr ls)= [IMov (Reg EBX) (Const (length expr))
                             ,IShl (Reg EBX) (Const 1)
                             ,IMov (RegOffset 0 ESI) (Reg EBX)
                             ,IMov (Reg EBX) (HexConst 0x00000000)
                             ,IMov (RegOffset 4 ESI) (Reg EBX)
                             ] 
unsetTag :: Reg -> Ty -> [Instruction]
unsetTag r ty = [ISub (Reg EAX) (typeTag ty)]
pairAlloc :: [Instruction]
pairAlloc
 = [ IMov (Reg EAX) (Reg ESI)
   , IAdd (Reg ESI) (Const 8)
   ]
setTag :: Reg -> Ty -> [Instruction]
setTag r ty = [ IAdd (Reg r) (typeTag ty) ]

compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg EAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is <> is') bs
  where
    (env', is')            = compileBind1 env b

compileBind1 :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind1 env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar i) (Reg EAX)]
    (i, env')          = pushEnv x env

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " <> show (void e)

--------------------------------------------------------------------------------
-- | Arithmetic
--------------------------------------------------------------------------------
arith :: Env -> AOp -> IExp -> IExp  -> [Instruction]
--------------------------------------------------------------------------------
arith env aop v1 v2
  =  assertType env v1 TNumber
  ++ assertType env v2 TNumber
  ++ IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : aop (Reg EAX) (Reg EBX)

addOp :: AOp
addOp a1 a2 = [ IAdd a1 a2
              , overflow
              ]

subOp :: AOp
subOp a1 a2 = [ ISub a1 a2
              , overflow
              ]

mulOp :: AOp
mulOp a1 a2 = [ ISar a1 (Const 1)
              , IMul a1 a2
              , overflow
              ]

overflow :: Instruction
overflow = IJo (DynamicErr ArithOverflow)

--------------------------------------------------------------------------------
-- | Dynamic Tests
--------------------------------------------------------------------------------
isType :: Ann -> Env -> IExp -> Ty -> [Instruction]
isType l env v ty
  =  cmpType env v ty
  ++ boolBranch  l IJe

-- | @assertType t@ tests if EAX is a value of type t and exits with error o.w.
assertType :: Env -> IExp -> Ty -> [Instruction]
assertType env v ty
  =   cmpType env v ty
  ++ [ IJne (DynamicErr (TypeError ty))    ]

cmpType :: Env -> IExp -> Ty -> [Instruction]
cmpType env v ty
  = [ IMov (Reg EAX) (immArg env v)
    , IMov (Reg EBX) (Reg EAX)
    , IAnd (Reg EBX) (typeMask ty)
    , ICmp (Reg EBX) (typeTag  ty)
    ]

--------------------------------------------------------------------------------
-- | Assignment
--------------------------------------------------------------------------------
assign :: (Repr a) => Reg -> a -> Instruction
assign r v = IMov (Reg r) (repr v)

tupleReserve :: Ann -> Int -> [Instruction]
tupleReserve l bytes
  = [ -- check for space
      IMov (Reg EAX) (LabelVar "HEAP_END")
    , ISub (Reg EAX) (Const bytes)
    , ICmp (Reg ESI) (Reg EAX)
    , IJl  (MemCheck (annTag l))   -- if ESI <= HEAP_END - size then OK else try_gc
    , IJe  (MemCheck (annTag l))
    , IMov (Reg EBX) (Reg ESP)
    ]
 ++ call (Builtin "try_gc") [ Reg ESI, wptr $ Const bytes, Reg EBP, Reg EBX ]
 ++ [ -- assume gc success if here; EAX holds new ESI
      IMov (Reg ESI) (Reg EAX)
    , ILabel (MemCheck (annTag l))
    ]
wptr :: Arg -> Arg
wptr a = Sized DWordPtr a
--------------------------------------------------------------------------------
-- | Function call
--------------------------------------------------------------------------------
call :: Label -> [Arg] -> [Instruction]
call f args
  =  [ IPush a | a <- reverse args ]
  ++ [ ICall f
     , IAdd (Reg ESP) (Const (4 * n))  ]
  where
    n = length args

param :: Env -> IExp -> Arg
param env v = Sized DWordPtr (immArg env v)

--------------------------------------------------------------------------------
-- | Branching
--------------------------------------------------------------------------------
branch :: Ann -> COp -> [Instruction] -> [Instruction] -> [Instruction]
branch l j falseIs trueIs = concat
  [ [ j lTrue ]
  , falseIs
  , [ IJmp lDone
    , ILabel lTrue  ]
  , trueIs
  , [ ILabel lDone ]
  ]
  where
    lTrue = BranchTrue i
    lDone = BranchDone i
    i     = annTag l

boolBranch :: Ann -> COp -> [Instruction]
boolBranch l j = branch l j [assign EAX False] [assign EAX True]

type AOp = Arg -> Arg -> [Instruction]
type COp = Label -> Instruction

stackVar :: Int -> Arg
stackVar i = RegOffset (-4 * i) EBP

--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007
