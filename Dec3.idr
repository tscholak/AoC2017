module Dec3

import Data.Vect

%default total

data Orientation = Up | Left | Down | Right

data MoverState : (position : (Int, Int)) -> (orientation : Orientation) -> Type where
     MkMoverState : (history : Vect n (Int, Int)) ->
                    MoverState position orientation

move : MoverState (x, y) orientation ->
       Either (MoverState (x, y) orientation)
              (Either (MoverState (x, y+1) Up)
                      (Either (MoverState (x-1, y) Left)
                              (Either (MoverState (x, y-1) Down)
                                      (MoverState (x+1, y) Right))))
move {x} {y} {orientation} (MkMoverState history) =
  case orientation of
    -- (x, y), Up, left-turn possible => (x-1, y), Left
    -- (x, y), Up, left-turn impossible, up possible => (x, y+1), Up
    -- (x, y), Up, left-turn impossible, up impossible => (x, y), Up
    Up => case elem (x-1, y) history of
      False => Right (Right (Left (MkMoverState ((x, y) :: history))))
      True => case elem (x, y+1) history of
        False => Right (Left (MkMoverState ((x, y) :: history)))
        True => Left (MkMoverState history)
    -- (x, y), Left, left-turn possible => (x, y-1), Downs
    -- (x, y), Left, left-turn impossible, left possible => (x-1, y), Left
    -- (x, y), Left, left-turn impossible, left impossible => (x, y), Left
    Left => case elem (x, y-1) history of
      False => Right (Right (Right (Left (MkMoverState ((x, y) :: history)))))
      True => case elem (x-1, y) history of
        False => Right (Right (Left (MkMoverState ((x, y) :: history))))
        True => Left (MkMoverState history)
    -- (x, y), Down, left-turn possible => (x+1, y), Right
    -- (x, y), Down, left-turn impossible, down possible => (x, y-1), Down
    -- (x, y), Down, left-turn impossible, down impossible => (x, y), Down
    Down => case elem (x+1, y) history of
      False => Right (Right (Right (Right (MkMoverState ((x, y) :: history)))))
      True => case elem (x, y-1) history of
        False => Right (Right (Right (Left (MkMoverState ((x, y) :: history)))))
        True => Left (MkMoverState history)
    -- (x, y), Right, left-turn possible => (x, y+1), Up
    -- (x, y), Right, left-turn impossible, right possible => (x+1, y), Right
    -- (x, y), Right, left-turn impossible, right impossible => (x, y), Right
    Right => case elem (x, y+1) history of
      False => Right (Left (MkMoverState ((x, y) :: history)))
      True => case elem (x+1, y) history of
        False => Right (Right (Right (Right (MkMoverState ((x, y) :: history)))))
        True => Left (MkMoverState history)

manhattanDistance : (Int, Int) -> (Int, Int) -> Int
manhattanDistance (x1, y1) (x2, y2) = abs (x1 - x2) + abs (y1 - y2)

walkDistance : MoverState (x, y) orientation -> (steps: Nat) -> Int
walkDistance (MkMoverState []) Z = 0
walkDistance (MkMoverState (h :: hs)) Z = manhattanDistance h $ last (h :: hs)
walkDistance state (S k) = case move state of
  Left state => walkDistance state k -- walkDistance state Z doesn't preserve totality for some reason
  Right (Left (state)) => walkDistance state k
  Right (Right (Left (state))) => walkDistance state k
  Right (Right (Right (Left (state)))) => walkDistance state k
  Right (Right (Right (Right (state)))) => walkDistance state k

dec3a : Int
dec3a = walkDistance {x = 0} {y = 0} {orientation = Down} (MkMoverState []) 361527
