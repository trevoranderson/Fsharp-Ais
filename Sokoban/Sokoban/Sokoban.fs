open System
open Astar

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
                    Some(setSquares g [ (Piece(Keeper(b)), closeCoord); (Moveable(under), g.KeeperPos) ] closeCoord)
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

let trivialHeuristic (g : GameState) = 0.0

let naiveManhattanHeuristic (g : GameState) = 
    let Boxes = 
        [ for r in 0..g.Squares.Length - 1 do
              for c in 0..g.Squares.[r].Length - 1 do
                  match g.Squares.[r].[c] with
                  | Piece(Box(_)) -> yield (r, c)
                  | _ -> () ]
    
    let Goals = 
        [ for r in 0..g.Squares.Length - 1 do
              for c in 0..g.Squares.[r].Length - 1 do
                  match g.Squares.[r].[c] with
                  | Moveable(Goal) | Piece(Box(Goal)) | Piece(Keeper(Goal)) -> yield (r, c)
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
                  | '0' -> Moveable(Blank)
                  | '1' -> Wall
                  | '2' -> Piece(Box(Blank))
                  | '3' -> Piece(Keeper(Blank))
                  | '4' -> Moveable(Goal)
                  | '5' -> Piece(Box(Goal))
                  | '6' -> Piece(Keeper(Goal))
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