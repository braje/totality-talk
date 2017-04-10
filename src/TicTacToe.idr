module TicTactoe

import Data.Fin as F
import Data.String as S
import Data.Vect as V

import ConsoleIO

%default total

-- Convenient alias for sized Matrix type
--
Matrix : Nat -> Nat -> Type -> Type
Matrix r c a = Vect r (Vect c a)

-- Filling in some of the game types
--
data Player = X | O

Eq Player where
  X == X = True
  O == O = True
  _ == _ = False

data GameResult = Win Player | Draw | InPlay

Board : Type
Board = Matrix 3 3 (Maybe Player)

mkEmptyBoard : Board
mkEmptyBoard = replicate 3 $ replicate 3 Nothing

idxMat : Fin n -> Fin m -> Matrix n m a -> a
idxMat r c m = index c (index r m)

gameRes : Board -> GameResult
gameRes b =
  if winFor X
  then Win X
  else if winFor O
       then Win O
       else if (all isJust (concat b))
            then Draw
            else InPlay

  where winFor : Player -> Bool
        winFor p =
          let bools = map (map (== (Just p))) b
          in  (any (all id) bools)
              || (any (all id) (transpose bools))
              || (all id (the (Vect _ Bool) [idxMat 0 0 bools, idxMat 1 1 bools, idxMat 2 2 bools]))
              || (all id (the (Vect _ Bool) [idxMat 2 0 bools, idxMat 1 1 bools, idxMat 0 2 bools]))

tryPlayPiece  : Fin 3 -> Fin 3 -> Player -> Board -> Maybe Board
tryPlayPiece r c p b =
  case idxMat r c b of
    Just _  => Nothing
    Nothing =>
      let newBoard = playPiece r c p b
      in  Just newBoard
  where playPiece : Fin 3 -> Fin 3 -> Player -> Board -> Board
        playPiece row col pc board =
          let theRow = index row board
          in  replaceAt row (replaceAt col (Just pc) theRow) board

computerPlay : Board -> Maybe Board
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

data Input
  = Index (Fin 3) (Fin 3)
  | Done
  | Oops

parseFin : String -> Maybe (Fin 3)
parseFin s = parseInteger s >>= \i => integerToFin i 3

readInput : ConsoleCmnd Input
readInput =
  do PutStr "\nEnter row and column indices separated by a space, q to quit: "
     rowS <- GetLine
     case span (/= ' ') rowS of
       ("q","")  => Pure Done
       (row,col) =>
         case (parseFin row, parseFin col) of
           (Just r, Just c) => Pure (Index r c)
           _                => Pure Oops

rowToString : Vect n (Maybe Player) -> String
rowToString = (++ "\n") . concat . intersperse "|" . map toStr
  where toStr : Maybe Player -> String
        toStr Nothing  = "   "
        toStr (Just X) = " X "
        toStr (Just O) = " O "

printBoard : Board -> ConsoleCmnd ()
printBoard b =
  traverse_ PutStr (intersperse "-----------\n" (map rowToString b))

data Result = XWin | XLose | NoWinner | Quitter

tictactoe : Board -> ConsoleIO Result
tictactoe b =
  do PutStr "The current state of affairs:\n\n"
     printBoard b
     input <- readInput
     case input of
       Index r c =>
         case (tryPlayPiece r c X b) of
           Nothing => do PutStr "You can't write on top of another player's piece!\n"
                         tictactoe b
           Just b  => do printBoard b
                         case gameRes b of
                           Win X  => Quit XWin
                           Win O  => Quit XLose
                           Draw   => Quit NoWinner
                           InPlay => computerPlay' b
       Done      => Quit Quitter
       Oops      => do PutStr "You mistyped.  Let's try again\n"
                       tictactoe b
   where computerPlay' : Board -> ConsoleIO Result
         computerPlay' b =
           case computerPlay b of
             Nothing => do PutStr "That's weird!\n"
                           Quit Quitter
             Just b' => case gameRes b' of
                          Win X  => Quit XWin
                          Win O  => Quit XLose
                          Draw   => Quit NoWinner
                          InPlay => tictactoe b'

main : IO ()
main = do
  putStrLn "How about a nice game of tic tac toe?\n\n"
  result <- runConsoleIO (tank 1000) (tictactoe mkEmptyBoard)
  putStrLn "\n"
  case result of
    Nothing       => putStrLn "Goodbye."
    Just XWin     => putStrLn "Congratulations, you win!"
    Just XLose    => putStrLn "Sorry, you lose!"
    Just NoWinner => putStrLn "Game is a draw!"
    Just Quitter  => putStrLn "Why you quit?"
  putStrLn "\n"
