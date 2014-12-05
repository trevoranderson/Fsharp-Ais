open System
open Astar
open Hungarian

type Passable = 
    | Blank
    | Goal

type OverPassable = 
    | Box of Passable
    | Keeper of Passable

type Square = 
    | Wall
    | Moveable of Passable
    | Piece of OverPassable

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
                       | Piece(Keeper(_)) -> true
                       | _ -> false) r
               match subIndex with
               | None -> false
               | Some(z) -> true) squares) with
    | None -> raise (System.Exception("Keeper not found on board"))
    | Some(row) -> 
        match (Array.tryFindIndex (fun r -> 
                   match r with
                   | Piece(Keeper(_)) -> true
                   | _ -> false) squares.[row]) with
        | None -> raise (System.Exception("Keeper expected, but not found"))
        | Some(col) -> (row, col)

let isGoal (g : GameState) = 
    match (Array.tryFind (fun r -> 
               match (Array.tryFind (fun c -> 
                          match c with
                          | Piece(Box(Blank)) -> true
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

let keeperSquare (g : GameState) = 
    let (kr, kc) = g.KeeperPos
    match g.Squares.[kr].[kc] with
    | Piece(Keeper(b)) -> b
    | _ -> raise (System.Exception("Expected keeper square"))

let nextStates (g : GameState) = 
    let (kr, kc) = g.KeeperPos
    let actions = getKeeperActions g
    let under = keeperSquare g
    actions
    |> List.map (fun a -> 
           match a with
           | Edge -> None
           | CloseTo((s, c)) -> 
               (match s with
                | Wall | Piece(Box(_)) -> None
                | Moveable(b) -> 
                    Some(setSquares g [ (Piece(Keeper(b)), c)
                                        (Moveable(under), g.KeeperPos) ] c)
                | Piece(Keeper(_)) -> raise (System.Exception("Is there more than one Keeper?")))
           | Central((closeSquare, closeCoord), (farSquare, farCoord)) -> 
               (match closeSquare with
                | Wall -> None
                | Moveable(b) -> 
                    Some(setSquares g [ (Piece(Keeper(b)), closeCoord)
                                        (Moveable(under), g.KeeperPos) ] closeCoord)
                | Piece(Keeper(_)) -> raise (System.Exception("Is there more than one Keeper?"))
                | Piece(Box(u)) -> 
                    (match farSquare with
                     | Wall | Piece(Box(_)) -> None
                     | Moveable(b) -> 
                         Some(setSquares g [ (Moveable(under), (kr, kc))
                                             (Piece(Keeper(u)), closeCoord)
                                             (Piece(Box(b)), farCoord) ] closeCoord)
                     | Piece(Keeper(_)) -> raise (System.Exception("Is there more than one Keeper?")))))
    |> List.choose (fun x -> 
           match x with
           | None -> None
           | Some(s) -> Some(s))
    |> Set.ofList

let getBoxes (g : GameState) = 
    [ for r in 0..g.Squares.Length - 1 do
          for c in 0..g.Squares.[r].Length - 1 do
              match g.Squares.[r].[c] with
              | Piece(Box(_)) -> yield (r, c)
              | _ -> () ]

let getGoals (g : GameState) = 
    [ for r in 0..g.Squares.Length - 1 do
          for c in 0..g.Squares.[r].Length - 1 do
              match g.Squares.[r].[c] with
              | Moveable(Goal) | Piece(Box(Goal)) | Piece(Keeper(Goal)) -> yield (r, c)
              | _ -> () ]

// Trivially admissable heuristic: 0. O(1)
let trivialHeuristic (g : GameState) = 0.0

// Adds total Manhattan distance of each box to its closest Goal + the closest way a player can get to a box to push it. O(n^2)
let naiveManhattanHeuristic (g : GameState) = 
    let Boxes = getBoxes g
    let minDist = 
        (List.fold 
             (fun bAcc (br, bc) -> 
             (List.fold (fun gAcc (gr, gc) -> min ((abs (br - gr)) + (abs (bc - gc))) gAcc) Int32.MaxValue (getGoals g)) 
             :: bAcc) [] Boxes) |> List.fold (+) 0
    let (kr, kc) = g.KeeperPos
    
    let playerDist = 
        ((Boxes |> List.fold (fun dist (br, bc) -> 
                       let curDist = (abs (br - kr)) + (abs (bc - kc))
                       if curDist < dist then curDist
                       else dist) Int32.MaxValue)
         - 1)
    double (minDist + playerDist)

// More sophisticated matching ensures each box maps to only one goal. O(n^3), but solves many maps much better
let HungarianHeuristic(g : GameState) = 
    let boxes = List.toArray (getBoxes g)
    let goals = List.toArray (getGoals g)
    let k = max boxes.Length goals.Length
    
    //Step0: Create a square matrix full of costs.  If things don't match, assume max cost
    let preliminaryCostMatrix = 
        [| for b in 0..k - 1 do
               yield b |]
        |> Array.map (fun b -> 
               [| for g in 0..k - 1 do
                      yield if b < boxes.Length && g < boxes.Length then 
                                (let (br, bc) = boxes.[b]
                                 let (gr, gc) = goals.[g]
                                 (abs (br - gr)) + (abs (bc - gc)))
                            else Int32.MaxValue |])
    
    let assignments = HungarianAlgorithm.Hungarian(preliminaryCostMatrix)
    let (kr, kc) = g.KeeperPos
    
    let playerDist = 
        ((boxes |> Array.fold (fun dist (br, bc) -> 
                       let curDist = (abs (br - kr)) + (abs (bc - kc))
                       if curDist < dist then curDist
                       else dist) Int32.MaxValue)
         - 1)
    double ((assignments |> Array.fold (fun acc elem -> 
                                let (r, c) = elem
                                acc + preliminaryCostMatrix.[r].[c]) 0)
            + playerDist)

[<EntryPoint>]
let main argv = 
    let input = System.IO.File.ReadAllLines("test.txt")
    let char2d = linesTo2dChars input
    
    let sq = 
        (Array.map (fun r -> 
             r |> (Array.map (fun c -> 
                       match c with
                       | '0' -> Moveable(Blank)
                       | '1' -> Wall
                       | '2' -> Piece(Box(Blank))
                       | '3' -> Piece(Keeper(Blank))
                       | '4' -> Moveable(Goal)
                       | '5' -> Piece(Box(Goal))
                       | '6' -> Piece(Keeper(Goal))
                       | _ -> raise (System.Exception("Invalid character in file input"))))) char2d)
    
    let k = 
        { KeeperPos = (getKeeperPos sq)
          Squares = sq }
    
    let compareDists = (HungarianHeuristic k, naiveManhattanHeuristic k, trivialHeuristic k)
    // Hungarian
    let startDist = HungarianHeuristic k
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    let res = Astar.AstarImpl.astar k nextStates isGoal (fun s -> 1.0) HungarianHeuristic
    stopWatch.Stop()
    printfn "%f ms elapsed at start distance: %f" stopWatch.Elapsed.TotalMilliseconds startDist
    // Manhattan
    let startDist = naiveManhattanHeuristic k
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    let res = Astar.AstarImpl.astar k nextStates isGoal (fun s -> 1.0) naiveManhattanHeuristic
    stopWatch.Stop()
    printfn "%f ms elapsed at start distance: %f" stopWatch.Elapsed.TotalMilliseconds startDist
    //Trivially admissable
    let startDist = trivialHeuristic k
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    let res = Astar.AstarImpl.astar k nextStates isGoal (fun s -> 1.0) trivialHeuristic
    stopWatch.Stop()
    printfn "%f ms elapsed at start distance: %f" stopWatch.Elapsed.TotalMilliseconds startDist
    0 // return an integer exit code
