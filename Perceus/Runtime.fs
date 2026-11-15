module Runtime

module T = Target
module H = heap
module Sig = signalStore

type State = 
    {
        Heap:H.Heap
        HeapNow: Sig.SignalStore
        HeapEarlier: Sig.SignalStore
        NextId: int
        UsedIds: Set<T.Var>
        Functions:T.FunctionContext
    }
