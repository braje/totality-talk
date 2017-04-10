---
title:  'Total Nonsense'
author:
- Timothy Braje
tags: [nothing, nothingness]
abstract: |
  This is the abstract.

  It consists of two paragraphs.
theme: white
transition: concave
slideNumber: true
width:  1920
height: 1200
css:
- https://fonts.googleapis.com/css?family=Volkhov
- css/custom.css
history: true
minScale: 0.5
maxScale: 3.0
...

## Introduction
### Totality vs. Turing Completeness

> Advocates of Total Functional Programming ... can prove prone to a false confession, namely that the price of functions which function is the loss of Turing-completeness.  In a total language, to construct `f: S -> T` is to promise a canonical `T` eventually, given a cononical `S`.

## Introduction
### Languages as Evidence

> Total functional languages remain _logically_ incomplete in the sense of Gödel ... the argument for general recursion asserts that logical inconsistency is a price worth paying for logical completeness, notwithstanding the loss of the language's value as _evidence_.

## Introduction
### Dishonesty

> Programmers are free to maintain that such _dishonesty_ is essential to their capacity to earn a living, but a new generation of programming technology enables some of us to offer and deliver a higher standard of guarantee.  _Faites vos jeus!_

## Outline

* Definitions
     * Turing Machines, etc.
     * Totality
* Implementing an Interactive Game, Responsibly
* Interpreting a Turing Machine, Formally

# Class Time {data-background-image="img/school-time.png"}

## Turing Machines & Completeness

 * ...

## Totality

A _total_ function, for _well-typed_ inputs either:

 * *Terminating* - Terminates with a well-typed result
 * *Productive* - Produces a well-typed finite prefix of a well-typed infinite result in finite time


## Partiality, Through Examples

```{.java .numberLines}
interface Map<K,V> {
  V get(Object) k);
  V remove(Object) k);
}

interface List<A> {
  A get(int i);
  int indexOf(Object o);
}
```

## Codata -- What It Means to be Productive

<!-- ```{.idris} -->
<!-- codata Stream a where -->
<!--   (:>) : a -> Stream a -> Stream a -->
<!-- ``` -->
```{.idris}
data Stream a where
  (::) : a -> Inf (Stream a) -> Stream a
```

. . .

```{.idris}
total
ones : Stream Int
ones = 1 :: ones
```
```{.idris}
partial
onesBad : List Int
onesBad = 1 :: onesBad
```

# How about a nice game of Tic-Tac-Toe? {data-background-image="img/POP_Bolt_range_02.png"}

## Some Type Setup

```{.idris .numberLines}
Matrix : Nat -> Nat -> Type -> Type
Matrix r c a = Vect r (Vect c a)

data Player = X | O

Eq Player where
  X == X = True
  O == O = True
  _ == _ = False

Board : Type
Board = Matrix 3 3 (Maybe Player)
```

* Rows and columns of board indexed by size
* Board cells contain `Maybe Player`{.idris}

## Playing a Piece

```{.idris .numberLines}
idxMat : Fin n -> Fin m -> Matrix n m a -> a
idxMat r c m = index c (index r m)
 
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
```

* Index into board with appropriately sized numbers

## Interact with Console, Try 1

```{.idris .numberLines}
data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

partial
run : InfIO -> IO ()
run (Do action cont) =
  do res <- action
     run (cont res)
```

* Infinite sequence of `IO`{.haskell} actions
* Can only run in partial context

## Need a Little Fuel

```{.idris .numberLines}
data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank    Z  = Dry
tank (S n) = More (tank n)
```

* Define some notion of 'willingness to wait'
* Fill tank as much as we want

## Running With Fuel, Totally

```{.idris .numberLines}
runWithFuel : Fuel -> InfIO -> IO ()
runWithFuel Dry      _
  = putStrLn "Out of fuel"
runWithFuel (More f) (Do act cont) 
  = do res <- act
       runWithFuel f (cont res)
```

* Keep executing commands, until tank is empty
* Guaranteed termination!

# We Could End There, but That Would Be Boring

## Honesty is also About Precision

```{.idris .numberLines}
data GameCmnd : Type -> Type where
  PutStr : String -> GameCmnd ()
  GetLine : GameCmnd String
  
  Pure : a -> GameCmnd a
  Bind : GameCmnd a -> (a -> GameCmnd b) -> GameCmnd b
  
data GameIO : Type -> Type where
  Quit : a -> GameIO a
  Do : GameCmnd a -> (a -> Inf (GameIO b)) -> GameIO b
```

* Define what parts of `IO`{.idris} we allow access to
* Allow programmer to build up programs that use that algebra

## Interpreter for `GameCmnd`{.haskell}

```{.idris .numberLines}
runGameCmnd : GameCmnd a -> IO a
runGameCmnd (PutStr s) = putStr s
runGameCmnd GetLine    = getLine
runGameCmnd (Pure a)   = pure a
runGameCmnd (Bind c f) =
  do res <- runGameCmnd c
     runGameCmnd (f res)
```

* Execute `GameCmnd`{.idris} within `IO`{.idris}
* We know we are safe from other `IO`{.idris} actions!

## Running the Action Stream

```{.idris .numberLines}
runGameIO : Fuel -> GameIO a -> IO (Maybe a)
runGameIO _ (Quit a) = pure (Just a)
runGameIO Dry _      =
  do putStrLn "Out of fuel"
     pure Nothing
runGameIO (More f) (Do cmnd cont) =
  do res <- runGameCmnd cmnd
     runGameIO f (cont res)
```

* Bored yet?

## Sanitizing User Input

```{.idris .numberLines}
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
```

## Define the Game Play

```{.idris .numberLines}
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
```

* Note: We are building up a potentially infinite sequence of `GameCmnd`{.idris}s, so we are allowed to recurse naturally

## Finally, Main()

```{.idris .numberLines}
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
```

# Turing Machines, Totally {data-background-image="img/ivory-tower.jpg"}

## G

# {data-background-image="img/LandinComputerScience.jpg"}

## Summary

* Codata make total languages Turing Complete
* The user decides how to interact with an _unfold_
* _Types_ can document possible interaction with the environment
* _Types_ document risk
* To argue for undocumented risk is to insist on ignorance of safety

## References

* [Totality vs. Turing Completeness? (Conor McBride)](https://personal.cis.strath.ac.uk/conor.mcbride/pub/Totality.pdf)
* [Type Driven Develoopment (Edwin Brady)](https://www.manning.com/books/type-driven-development-with-idris)
* [Introduction to the Theory of Computation (Michael Sipser)](http://www.cengage.com/c/introduction-to-the-theory-of-computation-3e-sipser/9781133187790)
