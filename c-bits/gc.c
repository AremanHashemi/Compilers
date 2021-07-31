#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include "types.h"

extern int* HEAP_END;
static int PRINTSIZE = 15;
int* dfsTuple(int* tupleStart);
typedef struct Frame_ {
  int *sp;
  int *bp;
} Frame;

Frame caller(int* stack_bottom, Frame frame){
  Frame callerFrame;
  int *bptr = frame.bp;
  if (bptr == stack_bottom){
    return frame;
  } else {
    callerFrame.sp = bptr + 1;
    callerFrame.bp = (int *) *bptr;
    return callerFrame;
  }
}

void print_stack(int* stack_top, int* first_frame, int* stack_bottom){
  Frame frame = {stack_top, first_frame };
  if (DEBUG) fprintf(stderr, "***** STACK: START sp=%p, bp=%p,bottom=%p *****\n", stack_top, first_frame, stack_bottom);
  do {
    if (DEBUG) fprintf(stderr, "***** FRAME: START *****\n");
    for (int *p = frame.sp; p < frame.bp; p++){
      if (DEBUG) fprintf(stderr, "  %p: %p\n", p, (int*)*p);
    }
    if (DEBUG) fprintf(stderr, "***** FRAME: END *****\n");
    frame    = caller(stack_bottom, frame);
  } while (frame.sp != stack_bottom);
  if (DEBUG) fprintf(stderr, "***** STACK: END *****\n");
}

void print_heap(int* heap, int size) {
  fprintf(stderr, "\n");
  for(int i = 0; i < size; i += 1) {
    fprintf(stderr
          , "  %d/%p: %p (%d)\n"
          , i
          , (heap + i)
          , (int*)(heap[i])
          , *(heap + i));
  }
}
/*
start from the top of the stack, keep going until you reach the bottom
increment by 1 word
Keep track of current base pointer if bp increment by 2 

*/
//TODO RETURN HIGHEST LIVE VALUE
////////////////////////////////////////////////////////////////////////////////
// FILL THIS IN, see documentation in 'gc.h' ///////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
int* mark( int* stack_top
         , int* first_frame
         , int* stack_bottom
         , int* heap_start)
{
  if (DEBUG) fprintf(stderr, "\n\n\n BEFORE MARK : \n");
  if (DEBUG) print_stack(stack_top, first_frame, stack_bottom);
  if (DEBUG) print_heap(heap_start, heap_start-HEAP_END);
  int* max_address = heap_start;
  int *p = stack_top;
  int* nextFrame = first_frame;
  while(p < stack_bottom){
      if(p == nextFrame){
        nextFrame =(int*) *p;
        p += 2;
        continue;
      }
      int stackValue = *p;
      if(is_tuple(stackValue)){
        int* address = int_addr(stackValue);
        if( address > max_address){
          max_address = address;
        }
        int* dfsMax = dfsTuple(address);
        if(dfsMax > max_address){
          max_address = dfsMax;
        }
      }
      ++p;
  }
  if (DEBUG) fprintf(stderr, "AFTER MARK: \n");
  if (DEBUG) print_stack(stack_top, first_frame, stack_bottom);
  if (DEBUG) print_heap(heap_start, PRINTSIZE);
  if (DEBUG) fprintf(stderr, "Max Address :%p \n\n\n",max_address);
  return max_address;
}
int* getMaxAddress(int* x, int* y){
  if(x > y){
    return x;
  }else{
    return y;
  }
}

int* dfsTuple(int* tupleStart){
  int* maxAddress = tupleStart; 
  tupleStart[1]  = 0x1;                   //Set live tag
  int length = tuple_size(tupleStart) + 2;
  if(length % 2 != 0) ++length;           //Padding for 8 byte allignment
  for(int i = 2; i < length; i++){        //Loop through elements lf tuples
    if(is_tuple(tupleStart[i])){
       int* localMax = dfsTuple(int_addr(tupleStart[i]));
       maxAddress = getMaxAddress(localMax, maxAddress);
    }
  }
  return maxAddress;
}



//two poitners next free slot=heapstart, keep old pointer
//one that tracks free slot, other traverses to next marked element
////////////////////////////////////////////////////////////////////////////////
// FILL THIS IN, see documentation in 'gc.h' ///////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
int* forward( int* heap_start
            , int* max_address)
{
  if (DEBUG) fprintf(stderr, "Before forward heap : \n");
  if (DEBUG) print_heap(heap_start, PRINTSIZE);

  int length = 0;
  int* freeSlot = heap_start;
  for(int* iter = heap_start; iter <= max_address; iter += length){
    length = tuple_size(iter) + 2;
    if(length % 2 != 0){
      length++;  //Padding for 8 byte 
    } 
    if(iter[1] != 0x0){
      iter[1] = (int)freeSlot + 1;
      freeSlot = length + freeSlot;
    }
  }
  if (DEBUG) fprintf(stderr, "AFTER FORWARD: \n");
  if (DEBUG) print_heap(heap_start, PRINTSIZE);
  if (DEBUG) fprintf(stderr, "Freeslot Address :%p \n",freeSlot);

  return freeSlot;
}

// 0| pointer1 | pointer2 | pointer1 


//Go through whole stack and whole heap if pointer in the stack 
//stack and you hit pointer, grab the metadata 2 update stack location 
// and in the heap

////////////////////////////////////////////////////////////////////////////////
// FILL THIS IN, see documentation in 'gc.h' ///////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
void redirect( int* stack_bottom
             , int* stack_top
             , int* first_frame
             , int* heap_start
             , int* max_address )
{
  if (DEBUG) fprintf(stderr, "BEFORE REDIRECT : \n");
  if (DEBUG) print_stack(stack_top, first_frame, stack_bottom);
  if (DEBUG) print_heap(heap_start, PRINTSIZE);
  

  int *p = stack_top;
  int* nextFrame = first_frame;
  while(p < stack_bottom){
      if(p == nextFrame){
        nextFrame =(int*) *p;
        p += 2;
        continue;
      }
      int stackValue = *p;
      if(is_tuple(stackValue)){
         int* address = int_addr(stackValue);
         *p = address[1];
       }
      ++p;
  }
  if (DEBUG) fprintf(stderr, "AFTER REDIRECT: \n");
  if (DEBUG) print_stack(stack_top, first_frame, stack_bottom);
  if (DEBUG) print_heap(heap_start, PRINTSIZE);
  
  return; 
}

//do another pass on the heap, move pointer to its reference metadata 
//overwite everything beyond max_address ->Heapend

//reset garbage collection metadata to 0 
////////////////////////////////////////////////////////////////////////////////
// FILL THIS IN, see documentation in 'gc.h' ///////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
void compact( int* heap_start
            , int* max_address
            , int* heap_end )
{ 
  if (DEBUG) fprintf(stderr, "Before compact heap : \n");
  if (DEBUG) print_heap(heap_start, PRINTSIZE);
  if (DEBUG) fprintf(stderr, "Freeslot Address :%p \n",heap_start);

  int length = 0;
  int* iter = 0;
  for(iter = heap_start; iter <= max_address; iter += length){
    length = tuple_size(iter) + 2;
    if(length % 2 != 0){
      ++length;
    }
    int* copyIter = int_addr(iter[1]);
    if(iter[1] != 0x0){                //If data is hot 
      for(int i = 0; i < length; ++i){
         copyIter[i] = iter[i];
      }
      copyIter[1] = 0x0;
    }
  }
  if (DEBUG) fprintf(stderr, "AFTER COMPACT: \n");
  if (DEBUG) print_heap(heap_start, PRINTSIZE);


  return;
}

////////////////////////////////////////////////////////////////////////////////
// Top-level GC function (you can leave this as is!) ///////////////////////////
////////////////////////////////////////////////////////////////////////////////

int* gc( int* stack_bottom
       , int* stack_top
       , int* first_frame
       , int* heap_start
       , int* heap_end )
{

  int* max_address = mark( stack_top
                         , first_frame
                         , stack_bottom
                         , heap_start );

  int* new_address = forward( heap_start
                            , max_address );

                     redirect( stack_bottom
                             , stack_top
                             , first_frame
                             , heap_start
                             , max_address );

                     compact( heap_start
                            , max_address
                            , heap_end );
  return new_address;
}
