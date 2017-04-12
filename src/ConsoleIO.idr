module ConsoleIO

%default total

public export
data ConsoleCmnd : Type -> Type where
  PutStr : String -> ConsoleCmnd ()
  GetLine : ConsoleCmnd String

  Pure : a -> ConsoleCmnd a
  Bind : ConsoleCmnd a -> (a -> ConsoleCmnd b) -> ConsoleCmnd b

export
Functor ConsoleCmnd where
  map f c = Bind c (Pure . f)

export
Applicative ConsoleCmnd where
  pure = Pure
  mf <*> ma = Bind mf (\f => map f ma)

public export
data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : ConsoleCmnd a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  export
  (>>=) : ConsoleCmnd a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

namespace CommandDo
  export
  (>>=) : ConsoleCmnd a -> (a -> ConsoleCmnd b) -> ConsoleCmnd b
  (>>=) = Bind

export
runConsoleCmnd : ConsoleCmnd a -> IO a
runConsoleCmnd (PutStr s) = putStr s
runConsoleCmnd GetLine    = getLine
runConsoleCmnd (Pure a)   = pure a
runConsoleCmnd (Bind c f) =
  do res <- runConsoleCmnd c
     runConsoleCmnd (f res)


  -- We need some fuel, for totality
  --
export
data Fuel = Dry | More (Lazy Fuel)

export
tank : Nat -> Fuel
tank    Z  = Dry
tank (S n) = More (tank n)

-- Bringing back infinity...
--

export partial
forever : Fuel
forever = More forever

-- forever
-- data Fuel = Dry | More (Lazy Fuel)

export
runConsoleIO : Fuel -> ConsoleIO a -> IO (Maybe a)
runConsoleIO _ (Quit a) = pure (Just a)
runConsoleIO Dry _      =
  do putStrLn "Out of fuel"
     pure Nothing
runConsoleIO (More f) (Do cmnd cont) =
  do res <- runConsoleCmnd cmnd
     runConsoleIO f (cont res)


-- Working with the console, badly
--
namespace InfIO

  data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO

  partial
  run : InfIO -> IO ()
  run (Do action cont) =
      do res <- action
         run (cont res)

  runWithFuel : Fuel -> InfIO -> IO ()
  runWithFuel Dry _ = putStrLn "Out of fuel"
  runWithFuel (More f) (Do act cont)
    = do res <- act
         runWithFuel f (cont res)
