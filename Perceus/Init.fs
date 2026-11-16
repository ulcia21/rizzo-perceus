module Init

let initialize sourceExpr functions stepleftlimit =
    let state: Runtime.State =
        { Heap = heap.empty
          HeapNow = signalStore.empty
          HeapEarlier = signalStore.empty
          NextId = 0
          UsedIds = Set.empty
          Functions = functions }

    let targetExpr = Elaborator.elaborate sourceExpr

    Interpreter.run stepleftlimit targetExpr state