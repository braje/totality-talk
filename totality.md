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
     * Turing Completeness
     * Totality
     * Termination (Halting Problem)
* Implementing a Game, Responsibly
* Interpreting a Turning Machine, Formally

# Class Time {data-background-image="img/school-time.png"}

## Turing Completeness

 * ...

## Totality, Informally

 * (from TDD)

## Totality, Formally

 * There are _expressions_ and _types_
 * Some expressions are _values_
 * Expressions reduce unless they are _values_
 * Every reduction sequence starting from a _well typed expression_ is finite
 * A _well typed_ expression eventually reduces to exactly one _value_

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

## ...But Servers

"If all programs terminate, how do we write an operating system?"

## Codata

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
ones = 1 :> ones
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
* Board cells contain `Maybe Player`

## Playing a Piece

```{.idris .numberLines}
idxMat : Fin n -> Fin m -> Matrix n m a -> a
idxMat r c m = index c (index r m)

tryPlayPiece  : Fin 3 -> Fin 3 -> Player -> Board -> Maybe (Board,Bool)
tryPlayPiece r c p b =
  case idxMat r c b of
    Just _  => Nothing
    Nothing =>
      let newBoard = playPiece r c p b
      in  Just (newBoard, isWin p newBoard)
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

* Infinite sequence of `IO` actions
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

## Running With Fuel

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

* Define what parts of `IO` we allow access to
* Allow programmer to build up programs that use that algebra

## Need to Interpret `GameCmnd`

```{.idris .numberLines}
runGameCmnd : GameCmnd a -> IO a
runGameCmnd (PutStr s)     = putStr s
runGameCmnd GetLine        = getLine
runGameCmnd (Pure a)   = pure a
runGameCmnd (Bind c f) =
  do res <- runGameCmnd c
     runGameCmnd (f res)
```

* Execute `GameCmnd` within `IO`
* We know we are safe from other `IO` actions!

## Running our Game

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

## Define the Game

```{.idris .numberLines}
tictactoe : Board -> GameIO Result
tictactoe b =
  do PutStr "The current state of affairs:\n\n"
     printBoard b
     input <- readInput
     case input of
       Index r c =>
         case (tryPlayPiece r c X b) of
           Nothing => do PutStr "You can't write on top of another player's piece!\n"
                         tictactoe b
           Just (b, True)  => do printBoard b
                                 Quit Win
           Just (b, False) =>
             case computerPlay b of
               Nothing => do PutStr "That's weird!\n"
                             Quit Quitter
               Just (b', True)   => do printBoard b'
                                       Quit Lose
               Just (b', False) => tictactoe b'
       Done      => Quit Quitter
       Oops      => do PutStr "You mistyped.  Let's try again"
                       tictactoe b
```

* Note: We are building up a potentially infinite sequence of `GameCmnd`s, so we are allowed to recurse naturally

## Finally, Main()

```{.idris .numberLines}
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
```

# Turing Machines, Totally {data-background-image="img/ivory-tower.jpg"}

## G

# {data-background-image="img/LandinComputerScience.jpg"}

## Summary

* Co-constructors make patterns, not values
* Interactive systems have episodoc evaluation
* _Types_ can document possible interaction with the environment
* _Types_ document risk
* To argue for undocumented risk is to insist on ignorance of safety

## Q.E.D.

* Codata make total languages Turning complete
* The user decides how to interact with an _unfold_
* Do anything you like, making weak promises
* Do some things making strong promises
* You can write an interpreter for a total language in itself, you just can't prove it converges

## References

