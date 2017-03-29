module TicTactoe

import Data.Fin as F
import Data.String as S
import Data.Vect

%default total


-- Convenient alias for sized Matrix type
--
Matrix : Nat -> Nat -> Type -> Type
Matrix r c a = Vect r (Vect c a)

transposeMat : Matrix r c a -> Matrix c r a
transposeMat []        = replicate _ []
transposeMat (x :: xs) =
  let xs' = transposeMat xs
  in  zipWith (::) x xs'

-- Filling in some of the game types
--

data PlayerSpot = X | O

Eq PlayerSpot where
  X == X = True
  O == O = True
  _ == _ = False

Board : Type
Board = Matrix 3 3 (Maybe PlayerSpot)

mkEmptyBoard : Board
mkEmptyBoard = replicate 3 $ replicate 3 Nothing

idxMat : Fin n -> Fin m -> Matrix n m a -> a
idxMat r c m = index c (index r m)


isWin : PlayerSpot -> Board -> Bool
isWin p b =
  let bools = map (map (== (Just p))) b
  in   (any (all id) bools)
    || (any (all id) (transpose bools))
    || (all id (the (Vect _ Bool) [idxMat 0 0 bools, idxMat 1 1 bools, idxMat 2 2 bools]))
    || (all id (the (Vect _ Bool) [idxMat 2 0 bools, idxMat 1 1 bools, idxMat 0 2 bools]))

tryPlayPiece  : Fin 3 -> Fin 3 -> PlayerSpot -> Board -> Maybe (Board,Bool)
tryPlayPiece r c p b =
  case idxMat r c b of
    Just _  => Nothing
    Nothing =>
      let newBoard = playPiece r c p b
      in  Just (newBoard, isWin p newBoard)
  where playPiece : Fin 3 -> Fin 3 -> PlayerSpot -> Board -> Board
        playPiece row col pc board =
          let theRow = index row board
          in  replaceAt row (replaceAt col (Just pc) theRow) board

computerPlay : Board -> Maybe (Board,Bool)
computerPlay b =
      tryPlayPiece 1 1 O b
  <+> tryPlayPiece 0 0 O b
  <+> tryPlayPiece 2 2 O b
  <+> tryPlayPiece 0 2 O b
  <+> tryPlayPiece 2 0 O b
  <+> tryPlayPiece 0 1 O b
  <+> tryPlayPiece 1 0 O b
  <+> tryPlayPiece 1 2 O b
  <+> tryPlayPiece 2 1 O b

-- Working with the console
--

namespace InfIO

  data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO

  partial
  run : InfIO -> IO ()
  run (Do action cont) =
    do res <- action
       run (cont res)


-- We need some fuel, for totality
--

data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank    Z  = Dry
tank (S n) = More (tank n)

runWithFuel : Fuel -> InfIO -> IO ()
runWithFuel Dry      _
  = putStrLn "Out of fuel"
runWithFuel (More f) (Do act cont) 
  = do res <- act
       runWithFuel f (cont res)


-- Bringing back infinity...
--

-- forever
-- data Fuel = Dry | More (Lazy Fuel)

-- Always better with an algebra...
--

namespace Cmnd
  data Command : Type -> Type where
    PutStr : String -> Command ()
    GetLine : Command String

  data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

runCommand : Command a -> IO a
runCommand (PutStr a) = putStr a
runCommand GetLine    = getLine

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit a) = pure (Just a)
run Dry  _        =
  do putStrLn "Out of fuel"
     pure Nothing
run (More f) (Do act cont) =
  do res <- runCommand act
     run f (cont res)


-- Make this our own...
--

data Input 
  = Index (Fin 3) (Fin 3)
  | Done
  | Oops

data GameCmnd : Type -> Type where
  PutStr : String -> GameCmnd ()
  GetLine : GameCmnd String
  PrintBoard : Board -> GameCmnd ()
  PlayPiece : Fin 3 -> Fin 3 -> PlayerSpot -> Board -> GameCmnd ( Board)

  Pure : a -> GameCmnd a
  Bind : GameCmnd a -> (a -> GameCmnd b) -> GameCmnd b

data GameIO : Type -> Type where
  Quit : a -> GameIO a
  Do : GameCmnd a -> (a -> Inf (GameIO b)) -> GameIO b

namespace ConsoleDo
  (>>=) : GameCmnd a -> (a -> Inf (GameIO b)) -> GameIO b
  (>>=) = Do

namespace CommandDo
  (>>=) : GameCmnd a -> (a -> GameCmnd b) -> GameCmnd b
  (>>=) = Bind


parseFin : String -> Maybe (Fin 3)
parseFin s = parseInteger s >>= \i => integerToFin i 3

readInput : GameCmnd Input
readInput =
  do PutStr "\nEnter row index, q to quit: "
     rowS <- GetLine
     case rowS of
       "q" => Pure Done
       row => case parseFin row of
                Nothing => Pure Oops
                Just r  => do PutStr "Enter column index, q to quit: "
                              colS <- GetLine
                              case colS of
                                "q" => Pure Done
                                col => case parseFin col of
                                         Nothing => Pure Oops
                                         Just c  => Pure (Index r c)

rowToString : Vect n (Maybe PlayerSpot) -> String
rowToString = concat . intersperse "|" . map toStr
  where toStr : Maybe PlayerSpot -> String
        toStr Nothing  = "   "
        toStr (Just X) = " X "
        toStr (Just O) = " O "

runGameCmnd : GameCmnd a -> IO a
runGameCmnd (PutStr s)     = putStr s
runGameCmnd GetLine        = getLine
runGameCmnd (PrintBoard b) =
  traverse_ putStrLn (intersperse "-----------" (map rowToString b))
runGameCmnd (PlayPiece r c p b) = pure b
runGameCmnd (Pure a)   = pure a
runGameCmnd (Bind c f) =
  do res <- runGameCmnd c
     runGameCmnd (f res)

data Result = Win | Lose | Quitter

runGameIO : Fuel -> GameIO a -> IO (Maybe a)
runGameIO _ (Quit a) = pure (Just a)
runGameIO Dry _      =
  do putStrLn "Out of fuel"
     pure Nothing
runGameIO (More f) (Do cmnd cont) =
  do res <- runGameCmnd cmnd
     runGameIO f (cont res)

tictactoe : Board -> GameIO Result
tictactoe b =
  do PutStr "The current state of affairs:\n\n"
     PrintBoard b
     input <- readInput
     case input of
       Index r c =>
         case (tryPlayPiece r c X b) of
           Nothing => do PutStr "You can't write on top of another player's piece!\n"
                         tictactoe b
           Just (b, True)  => do PrintBoard b 
                                 Quit Win
           Just (b, False) => 
             case computerPlay b of
               Nothing => do PutStr "That's weird!\n"
                             Quit Quitter
               Just (b', True)   => do PrintBoard b'
                                       Quit Lose
               Just (b', False) => tictactoe b'
       Done      => Quit Quitter
       Oops      => do PutStr "You mistyped.  Let's try again"
                       tictactoe b

main : IO ()
main = do
  putStrLn "How about a nice game of tic tac toe?"
  putStrLn "\n"
  result <- runGameIO (tank 1000) (tictactoe mkEmptyBoard)
  putStrLn "\n"
  case result of
    Nothing      => putStrLn "Goodbye."
    Just Win     => putStrLn "Congratulations, you win!"
    Just Lose    => putStrLn "Sorry, you lose!"
    Just Quitter => putStrLn "Why you quit?"
  putStrLn "\n"
  putStrLn "How about a nice game of chess?"
