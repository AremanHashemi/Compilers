# Scratch Compiler
A compiler for a new language. Compiler is written in Haskell, and uses C for the runtime garbage collecting


## Language features:
	- Double-word
	- Nested complex expression evaluation
	- Tuples
	- Functions
	- Recursion & tail recursion optimization 
	- Static Dynamic error checking:
		- Static & Dynamic type checking
		- Airity checking of function args
		- Static function/variable checking
		- Scope Checking
		- Duplication shadowing checking
		- Overflow checking 
		- Well formed expr checking
		- Dynamically checks heap space before
          allocation
	- Stack and heap variable binding
	- Complex expression evaluation  
	- Tags for conditional jumping
	- Smart runtime garbage collection in C 

