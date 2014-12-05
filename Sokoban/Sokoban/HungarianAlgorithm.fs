namespace Hungarian

open System

// Original (Java) implementation : https://github.com/w01fe/hungarian/blob/master/src/jvm/w01fe/hungarian/HungarianAlgorithm.java
module HungarianAlgorithm = 
    type private Mask = 
        | Nothing
        | Star
        | Prime
    
    type private MutCoord = 
        { mutable R : int
          mutable C : int }
    
    type private AlgoStep = 
        | S3
        | S4
        | S5
        | S6
        | S7
    
    // Step1 Subtract the smallest element of each row from every element in the row
    let private reduceRows (m : int [] []) = 
        m |> Array.map (fun r -> 
                 let rowmin = (r |> Array.fold (fun curm cost -> min curm cost) Int32.MaxValue)
                 r |> Array.map (fun elem -> elem - rowmin))
    
    // Step2
    let private starZeroes (cm : int [] []) (mutMask : Mask [] []) (mutRowCover : Mask []) (mutColCover : Mask []) = 
        for r in 0..cm.Length - 1 do
            for c in 0..cm.Length - 1 do
                if cm.[r].[c] = 0 then 
                    match (mutRowCover.[r], mutColCover.[c]) with
                    | (Nothing, Nothing) -> 
                        mutRowCover.[r] <- Star
                        mutColCover.[c] <- Star
                        mutMask.[r].[c] <- Star
                    | _ -> ()
    
    // Step 3
    let private s3 (mutMask : Mask [] []) (colCover : Mask []) = 
        for i in 0..mutMask.Length - 1 do
            for j in 0..mutMask.Length - 1 do
                match mutMask.[i].[j] with
                | Star -> colCover.[j] <- Star
                | _ -> ()
        let coveredCols = 
            colCover |> Array.fold (fun acc elem -> 
                            match elem with
                            | Star -> acc + 1
                            | _ -> acc) 0
        if coveredCols >= colCover.Length then S7
        else S4
    
    let private findUncoveredZero (rc : MutCoord) (cm : int [] []) (mutRowCover : Mask []) (mutColCover : Mask []) = 
        let mutable finished = false
        rc.R <- -1
        rc.C <- 0
        let mutable i = 0
        while (not finished) do
            for j in 0..cm.[i].Length - 1 do
                match (cm.[i].[j], mutRowCover.[i], mutColCover.[j]) with
                | (0, Nothing, Nothing) -> 
                    (let u0 = rc.R <- i
                     let u1 = rc.C <- j
                     let u2 = finished <- true
                     ())
                | _ -> ()
            i <- i + 1
            if i >= cm.Length then finished <- true
            else ()
        rc
    
    // Step 4
    let private s4 cm (mutMask : Mask [] []) (mutRowCover : Mask []) (mutColCover : Mask []) (mutZeroCoord : MutCoord) = 
        let mutable row_col = 
            { R = 0
              C = 0 }
        
        let mutable finished = false
        let mutable next = S5
        while (not finished) do
            row_col <- findUncoveredZero row_col cm mutRowCover mutColCover
            let (r, c) = (row_col.R, row_col.C)
            if r = (-1) then 
                finished <- true
                next <- S6
            else 
                mutMask.[r].[c] <- Prime
                let mutable starInRow = false
                for j in 0..mutMask.Length - 1 do
                    match mutMask.[r].[j] with
                    | Star -> 
                        (let u = starInRow <- true
                         
                         let uu = 
                             row_col <- { R = r
                                          C = j }
                         ())
                    | _ -> ()
                let (r, c) = (row_col.R, row_col.C)
                if starInRow then 
                    (mutRowCover.[r] <- Star
                     mutColCover.[c] <- Nothing)
                else 
                    (next <- S5
                     mutZeroCoord.R <- r
                     mutZeroCoord.C <- c
                     finished <- true)
        next
    
    let private findStarInCol (mutMask : Mask [] []) col = 
        let mutable r = -1
        for i in 0..mutMask.Length - 1 do
            match mutMask.[i].[col] with
            | Star -> r <- i
            | _ -> ()
        r
    
    let private findPrimeInRow (mutMask : Mask [] []) row = 
        let mutable c = -1
        for j in 0..mutMask.Length - 1 do
            match mutMask.[row].[j] with
            | Prime -> c <- j
            | _ -> ()
        c
    
    let private convertPath (mutMask : Mask [] []) (path : MutCoord []) count = 
        for i in 0..count do
            match mutMask.[path.[i].R].[path.[i].C] with
            | Star -> mutMask.[path.[i].R].[path.[i].C] <- Nothing
            | _ -> mutMask.[path.[i].R].[path.[i].C] <- Star
    
    let private erasePrimes (mutMask : Mask [] []) = 
        for i in 0..mutMask.Length - 1 do
            for j in 0..mutMask.Length - 1 do
                match mutMask.[i].[j] with
                | Prime -> mutMask.[i].[j] <- Nothing
                | _ -> ()
    
    let private clearCovers (mutRowCover : Mask []) (mutColCover : Mask []) = 
        for i in 0..mutRowCover.Length - 1 do
            mutRowCover.[i] <- Nothing
        for i in 0..mutColCover.Length - 1 do
            mutColCover.[i] <- Nothing
    
    let private s5 (mutMask : Mask [] []) (mutRowCover : Mask []) (mutColCover : Mask []) (mutZeroCoord : MutCoord) 
        (path : MutCoord []) = 
        let mutable count = 0
        path.[count].R <- mutZeroCoord.R
        path.[count].C <- mutZeroCoord.C
        let mutable finished = false
        while (not finished) do
            let r = findStarInCol mutMask path.[count].C
            if r >= 0 then 
                (let u0 = count <- count + 1
                 let u1 = path.[count].R <- r
                 let u2 = path.[count].C <- path.[count - 1].C
                 ())
            else finished <- true
            if (not finished) then 
                (let c = findPrimeInRow mutMask path.[count].R
                 count <- count + 1
                 path.[count].R <- path.[count - 1].R
                 path.[count].C <- c)
            else ()
        convertPath mutMask path count
        clearCovers mutRowCover mutColCover
        erasePrimes mutMask
        S3
    
    let private findSmallest (cm : int [] []) (mutRowCover : Mask []) (mutColCover : Mask []) = 
        let mutable minVal = Int32.MaxValue
        for i in 0..cm.Length - 1 do
            for j in 0..cm.Length - 1 do
                match (mutRowCover.[i], mutColCover.[j]) with
                | (Nothing, Nothing) -> 
                    if minVal > cm.[i].[j] then minVal <- cm.[i].[j]
                    else ()
                | _ -> ()
        minVal
    
    let private s6 (cm : int [] []) (mutRowCover : Mask []) (mutColCover : Mask []) = 
        let minVal = findSmallest cm mutRowCover mutColCover
        for i in 0..mutRowCover.Length - 1 do
            for j in 0..mutColCover.Length - 1 do
                match mutRowCover.[i] with
                | Star -> cm.[i].[j] <- (cm.[i].[j] + minVal)
                | _ -> ()
                match mutColCover.[j] with
                | Nothing -> cm.[i].[j] <- (cm.[i].[j] - minVal)
                | _ -> ()
        S4
    
    let Hungarian(rectangularCostMatrix : int [] []) = 
        // Pad the rectangular matrix to square
        let k = max rectangularCostMatrix.Length rectangularCostMatrix.[0].Length
        
        let preliminaryCostMatrix = 
            [| for i in 0..k - 1 do
                   yield i |]
            |> Array.map (fun i -> 
                   [| for j in 0..k - 1 do
                          yield if i < rectangularCostMatrix.Length && j < rectangularCostMatrix.[i].Length then 
                                    rectangularCostMatrix.[i].[j]
                                else Int32.MaxValue |])
        
        let costMatrix = reduceRows preliminaryCostMatrix
        let colCover = Array.init k (fun i -> Nothing)
        let rowCover = Array.init k (fun i -> Nothing)
        let mask = Array.init k (fun i -> Array.init k (fun j -> Nothing))
        starZeroes costMatrix mask rowCover colCover
        let mutable finished = false
        
        let mutable path = 
            Array.init (costMatrix.Length * costMatrix.Length + 2) (fun elem -> 
                { R = 0
                  C = 0 })
        
        let assignments = 
            Array.init costMatrix.Length (fun elem -> 
                { R = 0
                  C = 0 })
        
        let mutable zeroRC = 
            { R = 0
              C = 0 }
        
        let mutable curStep = S3
        while (not finished) do
            match curStep with
            | S3 -> curStep <- s3 mask colCover
            | S4 -> curStep <- s4 costMatrix mask rowCover colCover zeroRC
            | S5 -> curStep <- s5 mask rowCover colCover zeroRC path
            | S6 -> curStep <- s6 costMatrix rowCover colCover
            | S7 -> finished <- true
        let mutable assignmentsSeen = 0
        for i in 0..mask.Length - 1 do
            for j in 0..mask.Length - 1 do
                match mask.[i].[j] with
                | Star -> 
                    (if i < costMatrix.Length && j < costMatrix.Length then 
                         let u0 = assignments.[assignmentsSeen].R <- i
                         let u1 = assignments.[assignmentsSeen].C <- j
                         let u2 = assignmentsSeen <- assignmentsSeen + 1
                         ()
                     else ())
                | _ -> ()
        assignments |> Array.map (fun elem -> (elem.R, elem.C))
