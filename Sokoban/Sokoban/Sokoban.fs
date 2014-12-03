open System
open Astar

type Square = 
    | Blank
    | Wall
    | Box
    | Keeper
    | Goal
    | BoxGoal
    | KeeperGoal

type Coord = int * int

type GameState = 
    { KeeperPos : Coord
      Squares : Square [] [] }

type SquareCoord = Square * Coord

type KeeperAction = 
    | Edge
    | CloseTo of SquareCoord
    | Central of SquareCoord * SquareCoord

let explode (s : string) = 
    [ for c in s -> c ]

let linesTo2dChars l = Array.map (fun s -> List.toArray (explode s)) l

let getKeeperPos squares = 
    match (Array.tryFindIndex (fun r -> 
               let subIndex = 
                   Array.tryFindIndex (fun c -> 
                       match c with
                       | Keeper | KeeperGoal -> true
                       | _ -> false) r
               match subIndex with
               | None -> false
               | Some(z) -> true) squares) with
    | None -> raise (System.Exception("Keeper not found on board"))
    | Some(row) -> 
        match (Array.tryFindIndex (fun r -> 
                   match r with
                   | Keeper | KeeperGoal -> true
                   | _ -> false) squares.[row]) with
        | None -> raise (System.Exception("Keeper expected, but not found"))
        | Some(col) -> (row, col)

let isGoal (g : GameState) = 
    match (Array.tryFind (fun r -> 
               match (Array.tryFind (fun c -> 
                          match c with
                          | Box -> true
                          | _ -> false) r) with
               | None -> false
               | _ -> true) g.Squares) with
    | None -> true
    | _ -> false

let getKeeperActions (g : GameState) = 
    let (kr, kc) = g.KeeperPos
    let (kdr, kdc) = (g.Squares.Length - (kr + 1), g.Squares.[0].Length - (kc + 1))
    let squares = g.Squares
    [ (match kr with
       | 0 -> Edge
       | 1 -> CloseTo((squares.[kr - 1].[kc], (kr - 1, kc)))
       | _ -> Central(((squares.[kr - 1].[kc], (kr - 1, kc)), (squares.[kr - 2].[kc], (kr - 2, kc)))))
      (match kc with
       | 0 -> Edge
       | 1 -> CloseTo((squares.[kr].[kc - 1], (kr, kc - 1)))
       | _ -> Central(((squares.[kr].[kc - 1], (kr, kc - 1)), (squares.[kr].[kc - 2], (kr, kc - 2)))))
      (match kdr with
       | 0 -> Edge
       | 1 -> CloseTo((squares.[kr + 1].[kc], (kr + 1, kc)))
       | _ -> Central(((squares.[kr + 1].[kc], (kr + 1, kc)), (squares.[kr + 2].[kc], (kr + 2, kc)))))
      (match kdc with
       | 0 -> Edge
       | 1 -> CloseTo((squares.[kr].[kc + 1], (kr, kc + 1)))
       | _ -> Central(((squares.[kr].[kc + 1], (kr, kc + 1)), (squares.[kr].[kc + 2], (kr, kc + 2))))) ]

let neighbors r c (A : 'a [] []) = 
    [ if r > 0 then yield (r - 1, c)
      if r < Array.length A - 1 then yield (r + 1, c)
      if c > 0 then yield (r, c - 1)
      if c < Array.length A.[0] - 1 then yield (r, c + 1) ]

let copy2d arr = Array.map (fun x -> Array.copy x) arr

// Does not mutate gamestate, instead returns a new gamestate with the given transformations
let setSquares (g : GameState) (actions : SquareCoord list) nextKeeperPos = 
    let nextSquares = copy2d g.Squares
    let units = List.map (fun (s, (r, c)) -> Array.set nextSquares.[r] c s) actions
    { KeeperPos = nextKeeperPos
      Squares = nextSquares }

let nextStates (g : GameState) = 
    let (kr, kc) = g.KeeperPos
    let actions = getKeeperActions g
    
    let underKeeper = 
        (match g.Squares.[kr].[kc] with
         | Keeper -> Blank
         | _ -> Goal)
    actions
    |> List.map (fun a -> 
           match a with
           | Edge -> None
           | CloseTo((s, c)) -> 
               (match s with
                | Wall | Box | BoxGoal -> None
                | Blank -> 
                    Some(setSquares g [ (Keeper, c)
                                        (underKeeper, g.KeeperPos) ] c)
                | Goal -> 
                    Some(setSquares g [ (KeeperGoal, c)
                                        (underKeeper, g.KeeperPos) ] c)
                | Keeper | KeeperGoal -> raise (System.Exception("Is there more than one Keeper?")))
           | Central((closeSquare, closeCoord), (farSquare, farCoord)) -> 
               (match closeSquare with
                | Wall -> None
                | Blank -> 
                    Some(setSquares g [ (Keeper, closeCoord)
                                        (underKeeper, g.KeeperPos) ] closeCoord)
                | Goal -> 
                    Some(setSquares g [ (KeeperGoal, closeCoord)
                                        (underKeeper, g.KeeperPos) ] closeCoord)
                | Keeper | KeeperGoal -> raise (System.Exception("Is there more than one Keeper?"))
                | Box -> 
                    (match farSquare with
                     | Wall | Box | BoxGoal -> None
                     | Blank -> 
                         Some(setSquares g [ (underKeeper, (kr, kc))
                                             (Keeper, closeCoord)
                                             (Box, farCoord) ] closeCoord)
                     | Goal -> 
                         Some(setSquares g [ (underKeeper, (kr, kc))
                                             (Keeper, closeCoord)
                                             (BoxGoal, farCoord) ] closeCoord)
                     | Keeper | KeeperGoal -> raise (System.Exception("Is there more than one Keeper?")))
                | BoxGoal -> 
                    (match farSquare with
                     | Wall | Box | BoxGoal -> None
                     | Blank -> 
                         Some(setSquares g [ (underKeeper, (kr, kc))
                                             (KeeperGoal, closeCoord)
                                             (Box, farCoord) ] closeCoord)
                     | Goal -> 
                         Some(setSquares g [ (underKeeper, (kr, kc))
                                             (KeeperGoal, closeCoord)
                                             (BoxGoal, farCoord) ] closeCoord)
                     | Keeper | KeeperGoal -> raise (System.Exception("Is there more than one Keeper?")))))
    |> List.choose (fun x -> 
           match x with
           | None -> None
           | Some(s) -> Some(s))
    |> Set.ofList

let trivialHeuristic (g : GameState) = 0.0

let naiveManhattanHeuristic (g : GameState) = 
    let Boxes = 
        [ for r in 0..g.Squares.Length - 1 do
              for c in 0..g.Squares.[r].Length - 1 do
                  match g.Squares.[r].[c] with
                  | Box | BoxGoal -> yield (r, c)
                  | _ -> () ]
    
    let Goals = 
        [ for r in 0..g.Squares.Length - 1 do
              for c in 0..g.Squares.[r].Length - 1 do
                  match g.Squares.[r].[c] with
                  | Goal | BoxGoal | KeeperGoal -> yield (r, c)
                  | _ -> () ]
    
    let minDist = 
        (List.fold 
             (fun bAcc (br, bc) -> 
             (List.fold (fun gAcc (gr, gc) -> min (1 + (abs (br - gr)) + (abs (bc - gc))) gAcc) Int32.MaxValue Goals) 
             :: bAcc) [] Boxes) |> List.fold (+) 0
    double (minDist)

[<EntryPoint>]
let main argv = 
    let input = System.IO.File.ReadAllLines("test.txt")
    let char2d = linesTo2dChars input
    
    let sq = 
        (Array.map (fun r -> 
             (Array.map (fun c -> 
                  match c with
                  | '0' -> Blank
                  | '1' -> Wall
                  | '2' -> Box
                  | '3' -> Keeper
                  | '4' -> Goal
                  | '5' -> BoxGoal
                  | '6' -> KeeperGoal
                  | _ -> raise (System.Exception("Invalid character in file input"))) r)) char2d)
    
    let k = 
        { KeeperPos = (getKeeperPos sq)
          Squares = sq }
    
    let startDist = naiveManhattanHeuristic k
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    let res = Astar.AstarImpl.astar k nextStates isGoal (fun s -> 1.0) naiveManhattanHeuristic
    stopWatch.Stop()
    printfn "%f ms elapsed at start distance: %f" stopWatch.Elapsed.TotalMilliseconds startDist
    0 // return an integer exit code
