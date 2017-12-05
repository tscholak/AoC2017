module Dec3

import Data.Vect

%default total

data Orientation = Up | Left | Down | Right

data MoverState : (position : (Int, Int)) -> (orientation : Orientation) -> Type where
     MkMoverState : (history : Vect n (Int, Int)) -> (values : Vect n Int) ->
                    MoverState position orientation

-- TODO: Use foldl and zip instead
sumOfNeighbours : (history : Vect n (Int, Int)) -> (values : Vect n Int) -> (x, y : Int) -> Int
sumOfNeighbours [] [] x y = 0
sumOfNeighbours (h :: hs) (v :: vs) x y = case (abs (x - fst h), abs (y - snd h)) of
  (1, 1) => v + sumOfNeighbours hs vs x y
  _ => sumOfNeighbours hs vs x y

move : MoverState (x, y) orientation ->
       Either (MoverState (x, y) orientation)
              (Either (MoverState (x, y+1) Up)
                      (Either (MoverState (x-1, y) Left)
                              (Either (MoverState (x, y-1) Down)
                                      (MoverState (x+1, y) Right))))
move {x} {y} {orientation} (MkMoverState history values) =
  case orientation of
    -- (x, y), Up, left-turn possible => (x-1, y), Left
    -- (x, y), Up, left-turn impossible, up possible => (x, y+1), Up
    -- (x, y), Up, left-turn impossible, up impossible => (x, y), Up
    Up => case elem (x-1, y) history of
      False => Right (Right (Left (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values))))
      True => case elem (x, y+1) history of
        False => Right (Left (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values)))
        True => Left (MkMoverState history values)
    -- (x, y), Left, left-turn possible => (x, y-1), Downs
    -- (x, y), Left, left-turn impossible, left possible => (x-1, y), Left
    -- (x, y), Left, left-turn impossible, left impossible => (x, y), Left
    Left => case elem (x, y-1) history of
      False => Right (Right (Right (Left (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values)))))
      True => case elem (x-1, y) history of
        False => Right (Right (Left (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values))))
        True => Left (MkMoverState history values)
    -- (x, y), Down, left-turn possible => (x+1, y), Right
    -- (x, y), Down, left-turn impossible, down possible => (x, y-1), Down
    -- (x, y), Down, left-turn impossible, down impossible => (x, y), Down
    Down => case elem (x+1, y) history of
      False => Right (Right (Right (Right (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values)))))
      True => case elem (x, y-1) history of
        False => Right (Right (Right (Left (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values)))))
        True => Left (MkMoverState history values)
    -- (x, y), Right, left-turn possible => (x, y+1), Up
    -- (x, y), Right, left-turn impossible, right possible => (x+1, y), Right
    -- (x, y), Right, left-turn impossible, right impossible => (x, y), Right
    Right => case elem (x, y+1) history of
      False => Right (Left (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values)))
      True => case elem (x+1, y) history of
        False => Right (Right (Right (Right (MkMoverState ((x, y) :: history) ((sumOfNeighbours history values x y) :: values)))))
        True => Left (MkMoverState history values)

manhattanDistance : (Int, Int) -> (Int, Int) -> Int
manhattanDistance (x1, y1) (x2, y2) = abs (x1 - x2) + abs (y1 - y2)

walkDistance : (steps: Nat) -> MoverState (x, y) orientation -> Int
walkDistance Z (MkMoverState [] _) = 0
walkDistance Z (MkMoverState (h :: hs) _) = manhattanDistance h $ last (h :: hs)
walkDistance (S k) state = case move state of
  Left state => walkDistance k state -- walkDistance state Z doesn't preserve totality for some reason
  Right (Left (state)) => walkDistance k state
  Right (Right (Left (state))) => walkDistance k state
  Right (Right (Right (Left (state)))) => walkDistance k state
  Right (Right (Right (Right (state)))) => walkDistance k state

dec3a : Int
dec3a = walkDistance {x = 0} {y = 0} {orientation = Down} 361527 (MkMoverState [] [])

-- TODO: defined like this, it might never finish. how to make this total? max-attempts?
walkUntil : (p : Int -> Bool) -> MoverState (x, y) orientation -> Int
walkUntil p state = case move state of
    Left state' => recurse state'
    Right (Left (state')) => recurse state'
    Right (Right (Left (state'))) => recurse state'
    Right (Right (Right (Left (state')))) => recurse state'
    Right (Right (Right (Right (state')))) => recurse state'
  where
    recurse : MoverState (x', y') orientation' -> Int
