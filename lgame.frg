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

-- sudden death variant: players can move both neutral pieces instead of at most one
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
    some r5, c5, r6, c6: Int | {
      Game.neutral' = r5->c5 + r6->c6
    }
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

/*pred bad {
  eventually always ((Game.red != -2->-1 + -2->0 + -1->0 + 0->0) and (Game.blue != 1->0 + 1->-1 + 0->-1 + -1->-1))
}*/

pred twoNeutral {
  all a,b : Int | {a->b in Game.neutral implies a->b not in Game.neutral'}
}

// the theorem tests take minutes to run, recommend commenting out/singling out when testing theorem
test expect {

  -- translate: 21s, solve: <0.1s
  //vacuity: {traces} for 2 Int is sat
  -- translate: 18s, solve: <0.1s
  //canEndGame: {traces and eventually doNothing} for 2 Int is sat
  -- translate: 37s, solve: <0.1s
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
  -- if the game is not over, no one can move twice in a row
  -- translate: 171s, solve: 4s
  //sameTurnNotGameOver: {traces implies always (canMove => turn' != turn)} for 2 Int is theorem
  -- once the game ends (nobody takes a move during that turn) the game is permanently over (no further moves will be taken)
  -- translate: 166s, solve: 55s
  //permanentlyOver: {traces implies always (doNothing implies always doNothing)} for 2 Int is theorem
  -- checking for overconstraints in isLShape by testing if the red L can be in all of the corner orientations
  -- for each: translate: ~20-50s, solve: <0.5s
  /* redLinCorners:
    -- TOP LEFT CORNER
    {traces and eventually Game.red = -2->-1 + -2->-2 + -1->-2 + 0->-2} for 2 Int is sat
    -- translate: s, solve: s
    {traces and eventually Game.red = -1->-2 + -2->-2 + -2->-1 + -2->0} for 2 Int is sat
    -- TOP RIGHT CORNER
    -- translate: s, solve: s
    {traces and eventually Game.red = -1->1 + -2->1 + -2->0 + -2->-1} for 2 Int is sat
    -- translate: s, solve: s
    {traces and eventually Game.red = -2->0 + -2->1 + -1->1 + 0->1} for 2 Int is sat
    -- BOTTOM RIGHT CORNER
    -- translate: s, solve: s
    {traces and eventually Game.red = 1->0 + 1->1 + 0->1 + -1->1} for 2 Int is sat
    -- translate: s, solve: s
    {traces and eventually Game.red = 0->-2 + 1->-2 + 1->-1 + 1->0} for 2 Int is sat
    -- BOTTOM LEFT CORNER
    -- translate: s, solve: s
    {traces and eventually Game.red = 0->1 + 1->1 + 1->0 + 1->-1} for 2 Int is sat
    -- translate: s, solve: s
    {traces and eventually Game.red = 1->-1 + 1->-2 + 0->-2 + -1->-2} for 2 Int is sat */
  

  -- SUDDEN DEATH VARIANT TESTS 

  -- translate: 18s, solve: 0.2s
  //suddenDeathVacuity: {suddenDeathTraces} for 2 Int is sat
  -- translate: 19s, solve: <0.1s
  //suddenDeathNoNeutralMoves: {suddenDeathTraces and neutral' = neutral} for 2 Int is sat
  -- translate: 19s, solve: <0.1s
  //suddenDeathOneNeutralMove: {suddenDeathTraces and lone neutral' - neutral} for 2 Int is sat
  -- translate: 19s, solve: <0.1s
  //suddenDeathTwoNeutralMoves: {suddenDeathTraces and twoNeutral} for 2 Int is sat
  -- translate: 200s, solve: 0.3s
  //suddenDeathNoWinOneTurn: {suddenDeathTraces implies next_state canMove} for 2 Int is theorem
}

-- trace with a winner
-- generation time: 19s
run {traces and eventually doNothing} for 2 Int

-- infinite loop trace (no winner)
-- generation time: 38s
//run {traces and always canMove} for 2 Int

-- trace with a winner and at least 5 moves
-- generation time: 65s
//run {traces and next_state next_state next_state next_state canMove and eventually doNothing} for 2 Int

-- infinite loop trace, never loops back to first state
-- generation time: 60s
//run {traces and always canMove and next_state (always not init)} for 2 Int

-- sudden death trace with a winner
-- generation time: 19s
//run {suddenDeathTraces and eventually doNothing} for 2 Int

-- infinite loop sudden death trace (no winner)
-- generation time: 39s
//run {suddenDeathTraces and always canMove} for 2 Int