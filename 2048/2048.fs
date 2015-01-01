open System

type Square = 
    | Empty
    | Contains of int

let createboard() = 
    let rnd = System.Random()
    let r1 = rnd.Next(0, 4)
    let r2 = rnd.Next(0, 4)
    
    let v1 = 
        if rnd.Next(1, 11) = 1 then 2
        else 1
    
    let c1 = rnd.Next(0, 4)
    let c2 = rnd.Next(0, 4)
    
    let v2 = 
        if rnd.Next(1, 11) = 1 then 2
        else 1
    Array2D.init 4 4 (fun c r -> 
        if r = r1 && c = c1 then Contains(v1)
        else if r = r2 && c = c2 then Contains(v2)
        else Empty)

type Move = 
    | Up
    | Down
    | Left
    | Right

// Could also be column
let collapseRow row = 
    let rr = 
        row
        |> (Array.filter (fun elem -> 
                match elem with
                | Empty -> false
                | Contains(_) -> true))
        |> (Array.fold (fun acc elem -> 
                match (acc, elem) with
                | ([], y) -> [ y ]
                | (Contains(f) :: xs, Contains(s)) -> 
                    if f = s then Empty :: Contains(f + 1) :: xs
                    else Contains(s) :: Contains(f) :: xs
                | (Empty :: xs, Contains(s)) -> Contains(s) :: xs) [])
    
    let revved = List.rev rr
    let len = List.length revved
    if len < 4 then List.append revved (List.init (4 - len) (fun elem -> Empty)) |> List.toArray
    else revved |> List.toArray

let compareBoards (b : Square [,]) (n : Square [,]) = 
    match [ for r in 0..3 do
                for c in 0..3 do
                    match (b.[r, c], n.[r, c]) with
                    | (Empty, Empty) -> ()
                    | (Contains(x), Contains(y)) when x = y -> ()
                    | _ -> yield false ] with
    | [] -> true
    | x :: xs -> false

let applymove (b : Square [,]) m = 
    let next = 
        match m with
        | Up -> 
            let nboard = 
                [| b.[0..3, 0] |> collapseRow
                   b.[0..3, 1] |> collapseRow
                   b.[0..3, 2] |> collapseRow
                   b.[0..3, 3] |> collapseRow |]
            Array2D.init 4 4 (fun c r -> nboard.[r].[c])
        | Down -> 
            let nboard = 
                [| b.[0..3, 0]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev
                   b.[0..3, 1]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev
                   b.[0..3, 2]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev
                   b.[0..3, 3]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev |]
            Array2D.init 4 4 (fun c r -> nboard.[r].[c])
        | Left -> 
            let nboard = 
                [| b.[0, 0..3] |> collapseRow
                   b.[1, 0..3] |> collapseRow
                   b.[2, 0..3] |> collapseRow
                   b.[3, 0..3] |> collapseRow |]
            Array2D.init 4 4 (fun r c -> nboard.[r].[c])
        | Right -> 
            let nboard = 
                [| b.[0, 0..3]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev
                   b.[1, 0..3]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev
                   b.[2, 0..3]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev
                   b.[3, 0..3]
                   |> Array.rev
                   |> collapseRow
                   |> Array.rev |]
            Array2D.init 4 4 (fun r c -> nboard.[r].[c])
    if compareBoards b next then ()
    else 
        let coords = 
            [| for r in 0..3 do
                   for c in 0..3 do
                       match next.[r, c] with
                       | Empty -> yield (r, c)
                       | Contains(_) -> () |]
        
        let rnd = System.Random()
        let (r, c) = coords.[rnd.Next(Array.length coords)]
        
        let vr = 
            if rnd.Next(1, 11) = 1 then 2
            else 1
        next.[r, c] <- Contains(vr)
    next

let printBoard (b : Square [,]) = 
    for r in 0..3 do
        printf ("\n")
        for c in 0..3 do
            match b.[r, c] with
            | Empty -> printf ("_ ")
            | Contains(x) -> printf "%i " x

let inputToDirection() = 
    match Console.ReadLine() with
    | "w" -> Up
    | "a" -> Left
    | "s" -> Down
    | _ -> Right //"d"

[<EntryPoint>]
let main argv = 
    let mutable t = createboard()
    while true do
        printBoard t
        let ui = inputToDirection()
        let next = applymove t ui
        t <- next
    0 // return an integer exit code
