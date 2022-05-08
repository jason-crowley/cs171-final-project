#lang forge

option problem_type temporal
option max_tracelength 10

abstract sig Player {}
one sig Red, Blue extends Player {}

one sig Game {
  var red: set Int -> Int,
  var blue: set Int -> Int,
  var neutral: set Int -> Int,
  var turn: one Player
}

// Game board is indexed from -2 to 1 to avoid overflow
pred init {
  -- red L starting position
  Game.red =
    -2 -> -1 +
    -2 ->  0 +
    -1 ->  0 +
    0 ->  0
  -- blue L starting position
  Game.blue =
    1 ->  0 +
    1 -> -1 +
    0 -> -1 +
    -1 -> -1
  -- netural pieces starting positions
  Game.neutral =
    -2 -> -2 +
    1 ->  1
  -- red player takes the first move
  Game.turn = Red
}

pred adjacent[x: Int, y: Int] {
  subtract[max[x + y], min[x + y]] = 1
}

pred rowAdjacent[r1, c1, r2, c2: Int] {
  adjacent[r1, r2]
  c1 = c2
}

pred colAdjacent[r1, c1, r2, c2: Int] {
  r1 = r2
  adjacent[c1, c2]
}

pred isLShape[r1, c1, r2, c2, r3, c3, r4, c4: Int] {
  {
    colAdjacent[r1, c1, r2, c2]
    colAdjacent[r2, c2, r3, c3]
    rowAdjacent[r3, c3, r4, c4]
    c1 != c3 
  } or {
    rowAdjacent[r1, c1, r2, c2]
    rowAdjacent[r2, c2, r3, c3]
    colAdjacent[r3, c3, r4, c4]
    r1 != r3
  }
}

pred wellFormed {
  always {
    #red = 4
    #blue = 4
    #neutral = 2

    no red & blue
    no red & neutral
    no blue & neutral

    some r1, c1, r2, c2, r3, c3, r4, c4: Int | {
      Game.red = r1->c1 + r2->c2 + r3->c3 + r4->c4
      isLShape[r1, c1, r2, c2, r3, c3, r4, c4]
    }

    some r1, c1, r2, c2, r3, c3, r4, c4: Int | {
      Game.blue = r1->c1 + r2->c2 + r3->c3 + r4->c4
      isLShape[r1, c1, r2, c2, r3, c3, r4, c4]
    }
  }
}

pred validMove[r1, c1, r2, c2, r3, c3, r4, c4: Int] {
  isLShape[r1, c1, r2, c2, r3, c3, r4, c4]
  let L = r1->c1 + r2->c2 + r3->c3 + r4->c4 | {
    Game.turn = Red => {
      L != Game.red
      L in Int->Int - Game.(blue + neutral)
    } else {
      L != Game.blue
      L in Int->Int - Game.(red + neutral)
    }
  }
}

pred canMove {
  some r1, c1, r2, c2, r3, c3, r4, c4: Int |
    validMove[r1, c1, r2, c2, r3, c3, r4, c4]
}

pred isWinner[p: Player] {
  Game.turn != p and not canMove
}

pred trans[r1, c1, r2, c2, r3, c3, r4, c4: Int] {
  validMove[r1, c1, r2, c2, r3, c3, r4, c4]
  let L = r1->c1 + r2->c2 + r3->c3 + r4->c4 | {
    Game.turn = Red => {
      Game.red' = L
      blue' = blue
    } else {
      Game.blue' = L
      red' = red
    }
    lone neutral' - neutral
    turn' != turn
  }
}

pred suddenDeathTrans[r1, c1, r2, c2, r3, c3, r4, c4: Int] {
  validMove[r1, c1, r2, c2, r3, c3, r4, c4]
  let L = r1->c1 + r2->c2 + r3->c3 + r4->c4 | {
    Game.turn = Red => {
      Game.red' = L
      blue' = blue
    } else {
      Game.blue' = L
      red' = red
    }
    turn' != turn
  }
}

pred doNothing {
  -- the game is over, so nothing changes
  red' = red
  blue' = blue
  neutral' = neutral
  turn' = turn
}

pred traces {
  init
  wellFormed
  always {
    canMove => {
      some r1, c1, r2, c2, r3, c3, r4, c4: Int | {
        trans[r1, c1, r2, c2, r3, c3, r4, c4]
      }
    } else doNothing
  }
}

pred suddenDeathTraces {
  init
  wellFormed
  always {
    canMove => {
      some r1, c1, r2, c2, r3, c3, r4, c4: Int | {
          suddenDeathTrans[r1, c1, r2, c2, r3, c3, r4, c4]
      }
    } else doNothing
  }
}

---- Testing ----

pred noNeutralMoves {
  always {
    Game.neutral =
     1 -> -2 +
    -2 ->  1
  }
}

// the theorem tests take minutes to run, recommend commenting out/singling out when testing theorem
test expect {
  -- translate: 20s, solve: <0.1s
  vacuity: {traces} for 2 Int is sat
  -- translate: 4s, solve: <0.1s (implies not and?? better runtime but is this what we want?)
  //canEndGame: {traces and eventually doNothing} for 2 Int is sat
  -- translate: 5s, solve: <0.1s (implies not and?? better runtime but is this what we want?)
  //canPlayInfinite: {traces and always canMove} for 2 Int is sat
  -- translate: 174s (109s with symmetry-breaking), solve: <0.1s 
  //noWinUnlessNeutralMove: {(traces and noNeutralMoves) implies always canMove} for 2 Int is theorem
  -- translate: 197s, solve: <0.1s
  //noWinOneTurn: {traces implies next_state canMove} for 2 Int is theorem
  -- translate: 22s, solve: <0.1s
  //canWinTwoTurns: {traces and next_state next_state (some p: Player | isWinner[p])} for 2 Int is sat
  -- translate: 33s, solve: 0.2s
  //redCanWin: {traces and eventually isWinner[Red]} for 2 Int is sat
  -- translate: 22s, solve: 0.2s
  //blueCanWin: {traces and eventually isWinner[Blue]} for 2 Int is sat
  -- translate: 171s, solve: 4s
  //sameTurnNotGameOver: {traces implies always (canMove => turn' != turn)} for 2 Int is theorem
  /* LinCorners:
    -- top left corner
    -- translate: 119s, solve: 0.6s
    {traces and eventually Game.red = -2->-1 + -2->-2 + -1->-2 + 0->-2} for 2 Int is sat
    {traces and eventually Game.red == -1->-2 + -2->-2 + -2->-1 + -2->0} for 2 Int is sat
    -- top right corner
    {traces and eventually Game.red == -1->1 + -2->1 + -2->0 + -2->-1} for 2 Int is sat
    {traces and eventually Game.red == -2->0 + -2->1 + -1->1 + 0->1} for 2 Int is sat
    -- bottom right corner
    {traces and eventually Game.red == 1->0 + 1->1 + 0->1 + -1->1} for 2 Int is sat
    {traces and eventually Game.red == 0->-2 + 1->-2 + 1->-1 + 1->0} for 2 Int is sat
    -- botttom left corner
    {traces and eventually Game.red == 0->1 + 1->1 + 1->0 + 1->-1} for 2 Int is sat
    {traces and eventually Game.red == 1->-1 + 1->-2 + 0->-2 + 1->-2} for 2 Int is sat */
    /// tests for sudden death trans
}

run { traces } for 2 Int
