#lang forge

option problem_type temporal
option max_tracelength 10

abstract sig Player {}
one sig Red, Blue extends Player {}

sig L {
  cells: set Int -> Int
}

one sig Game {
  var red: one L,
  var blue: one L,
  var neutral: set Int -> Int,
  var turn: one Player
}

// Game board is indexed from -2 to 1 to avoid overflow
pred init {
  -- red L starting position
  Game.red.cells =
    -2 -> -1 +
    -2 ->  0 +
    -1 ->  0 +
     0 ->  0
  -- blue L starting position
  Game.blue.cells =
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
    #neutral = 2

    no red.cells & blue.cells
    no (red + blue).cells & neutral
  }
}

pred validMove[l: one L] {
  Game.turn = Red => {
    l != Game.red
    l.cells in Int->Int - Game.(blue.cells + neutral)
  } else {
    l != Game.blue
    l.cells in Int->Int - Game.(red.cells + neutral)
  }
}

pred canMove {
  some l: L | validMove[l]
}

pred isWinner[p: Player] {
  Game.turn != p and not canMove
}

pred trans[l: one L] {
  validMove[l]
  Game.turn = Red => {
    Game.red' = l
    blue' = blue
  } else {
    Game.blue' = l
    red' = red
  }
  lone neutral' - neutral
  turn' != turn
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
      some l: L | trans[l]
    } else doNothing
  }
}

-- sudden death variant: players can move both neutral pieces instead of at most one
pred suddenDeathTrans[l: one L] {
  validMove[l]
  Game.turn = Red => {
    Game.red' = l
    blue' = blue
  } else {
    Game.blue' = l
    red' = red
  }
  turn' != turn
  some r5, c5, r6, c6: Int | {
    Game.neutral' = r5->c5 + r6->c6
  }
}

pred suddenDeathTraces {
  init
  wellFormed
  always {
    canMove => {
      some l: L | suddenDeathTrans[l]
    } else doNothing
  }
}

---- Testing ----

// for no neutral moves tests
pred noNeutralMoves {
  always {
    Game.neutral =
      -2 -> -2 +
       1 ->  1
  }
}

// for sudden death two neutral test
pred twoNeutral {
  no neutral & neutral'
}

inst Ls {
  L =
    `L00 + `L01 + `L02 + `L03 + `L04 + `L05 +
    `L06 + `L07 + `L08 + `L09 + `L10 + `L11 +
    `L12 + `L13 + `L14 + `L15 + `L16 + `L17 +
    `L18 + `L19 + `L20 + `L21 + `L22 + `L23 +
    `L24 + `L25 + `L26 + `L27 + `L28 + `L29 +
    `L30 + `L31 + `L32 + `L33 + `L34 + `L35 +
    `L36 + `L37 + `L38 + `L39 + `L40 + `L41 +
    `L42 + `L43 + `L44 + `L45 + `L46 + `L47

  cells =
    -- normal Ls
    `L00->(-2->-2 + -1->-2 +  0->-2 +  0->-1) +
    `L01->(-2->-1 + -1->-1 +  0->-1 +  0-> 0) +
    `L02->(-2-> 0 + -1-> 0 +  0-> 0 +  0-> 1) +
    `L03->(-1->-2 +  0->-2 +  1->-2 +  1->-1) +
    `L04->(-1->-1 +  0->-1 +  1->-1 +  1-> 0) +
    `L05->(-1-> 0 +  0-> 0 +  1-> 0 +  1-> 1) +
    -- upside-down Ls
    `L06->( 0->-2 + -1->-2 + -2->-2 + -2->-1) +
    `L07->( 0->-1 + -1->-1 + -2->-1 + -2-> 0) +
    `L08->( 0-> 0 + -1-> 0 + -2-> 0 + -2-> 1) +
    `L09->( 1->-2 +  0->-2 + -1->-2 + -1->-1) +
    `L10->( 1->-1 +  0->-1 + -1->-1 + -1-> 0) +
    `L11->( 1-> 0 +  0-> 0 + -1-> 0 + -1-> 1) +
    -- backwards Ls
    `L12->(-2->-1 + -1->-1 +  0->-1 +  0->-2) +
    `L13->(-2-> 0 + -1-> 0 +  0-> 0 +  0->-1) +
    `L14->(-2-> 1 + -1-> 1 +  0-> 1 +  0-> 0) +
    `L15->(-1->-1 +  0->-1 +  1->-1 +  1->-2) +
    `L16->(-1-> 0 +  0-> 0 +  1-> 0 +  1->-1) +
    `L17->(-1-> 1 +  0-> 1 +  1-> 1 +  1-> 0) +
    -- backwards upside-down Ls
    `L18->(-2->-1 + -1->-1 +  0->-1 + -2->-2) +
    `L19->(-2-> 0 + -1-> 0 +  0-> 0 + -2->-1) +
    `L20->(-2-> 1 + -1-> 1 +  0-> 1 + -2-> 0) +
    `L21->(-1->-1 +  0->-1 +  1->-1 + -1->-2) +
    `L22->(-1-> 0 +  0-> 0 +  1-> 0 + -1->-1) +
    `L23->(-1-> 1 +  0-> 1 +  1-> 1 + -1-> 0) +
    -- everything above transposed
    -- normal Ls
    `L24->(-2->-2 + -2->-1 + -2-> 0 + -1-> 0) +
    `L25->(-1->-2 + -1->-1 + -1-> 0 +  0-> 0) +
    `L26->( 0->-2 +  0->-1 +  0-> 0 +  1-> 0) +
    `L27->(-2->-1 + -2-> 0 + -2-> 1 + -1-> 1) +
    `L28->(-1->-1 + -1-> 0 + -1-> 1 +  0-> 1) +
    `L29->( 0->-1 +  0-> 0 +  0-> 1 +  1-> 1) +
    -- upside-down Ls
    `L30->(-2-> 0 + -2->-1 + -2->-2 + -1->-2) +
    `L31->(-1-> 0 + -1->-1 + -1->-2 +  0->-2) +
    `L32->( 0-> 0 +  0->-1 +  0->-2 +  1->-2) +
    `L33->(-2-> 1 + -2-> 0 + -2->-1 + -1->-1) +
    `L34->(-1-> 1 + -1-> 0 + -1->-1 +  0->-1) +
    `L35->( 0-> 1 +  0-> 0 +  0->-1 +  1->-1) +
    -- backwards Ls
    `L36->(-1->-2 + -1->-1 + -1-> 0 + -2-> 0) +
    `L37->( 0->-2 +  0->-1 +  0-> 0 + -1-> 0) +
    `L38->( 1->-2 +  1->-1 +  1-> 0 +  0-> 0) +
    `L39->(-1->-1 + -1-> 0 + -1-> 1 + -2-> 1) +
    `L40->( 0->-1 +  0-> 0 +  0-> 1 + -1-> 1) +
    `L41->( 1->-1 +  1-> 0 +  1-> 1 +  0-> 1) +
    -- backwards upside-down Ls
    `L42->(-1->-2 + -1->-1 + -1-> 0 + -2->-2) +
    `L43->( 0->-2 +  0->-1 +  0-> 0 + -1->-2) +
    `L44->( 1->-2 +  1->-1 +  1-> 0 +  0->-2) +
    `L45->(-1->-1 + -1-> 0 + -1-> 1 + -2->-1) +
    `L46->( 0->-1 +  0-> 0 +  0-> 1 + -1->-1) +
    `L47->( 1->-1 +  1-> 0 +  1-> 1 +  0->-1)
}


-- Ls Tests
test expect {
  -- translate: 3s, solve: <0.1s
  // allLs: {
  //   all r1, c1, r2, c2, r3, c3, r4, c4: Int | {
  //     isLShape[r1, c1, r2, c2, r3, c3, r4, c4] => {
  //       one l: L | l.cells = r1->c1 + r2->c2 + r3->c3 + r4->c4
  //     }
  //   }
  // } for 2 Int for Ls is sat
}


-- Standard Game Tests
test expect {
  -- translate: 0.3s, solve: <0.1s
  // vacuity: {traces} for 2 Int for Ls is sat
  -- the game can end (there can be a winner)
  -- translate: 0.3s, solve: <0.1s
  // canEndGame: {traces and eventually doNothing} for 2 Int for Ls is sat
  -- the game can never end
  -- translate: 3s, solve: <0.1s
  // canPlayInfinite: {traces and always canMove} for 2 Int for Ls is sat
  -- a player can choose to move no neutral piece
  -- translate: 0.3s, solve: <0.1s
  // noNeutralMoveVacuity: {traces noNeutralMoves} for 2 Int for Ls is sat
  -- there can't be a winner without a neutral piece being moved
  -- translate: 1s, solve: 2.2s
  // noWinUnlessNeutralMove: {(traces and noNeutralMoves) implies always canMove} for 2 Int for Ls is theorem
  -- can't win on the first turn
  -- translate: 1.1s, solve: 0.2s
  // noWinOneTurn: {traces implies next_state canMove} for 2 Int for Ls is theorem
  -- can win in two turns
  -- translate: 0.2s, solve: <0.1s
  // canWinTwoTurns: {traces and next_state next_state (some p: Player | isWinner[p])} for 2 Int for Ls is sat
  -- red can win
  -- translate: 0.3s, solve: 0.4s
  // redCanWin: {traces and eventually isWinner[Red]} for 2 Int for Ls is sat
  -- blue can win
  -- translate: 0.3s, solve: <0.1s
  // blueCanWin: {traces and eventually isWinner[Blue]} for 2 Int for Ls is sat
  -- if the game is not over, no one can move twice in a row
  -- translate: 1s, solve: 27s
  // sameTurnNotGameOver: {traces implies always (canMove => turn' != turn)} for 2 Int for Ls is theorem
  -- once the game ends (nobody takes a move during that turn) the game is permanently over (no further moves will be taken)
  -- translate: 1s, solve: 234s
  // permanentlyOver: {traces implies always (doNothing implies always doNothing)} for 2 Int for Ls is theorem
}


-- Sudden Death Variant Tests
test expect {
  -- translate: 0.3s, solve: <0.1s
  // suddenDeathVacuity: {suddenDeathTraces} for 2 Int for Ls is sat
  -- you can move 0 neutral pieces in the sudden death variant
  -- translate: 0.3s, solve: <0.1s
  // suddenDeathNoNeutralMoves: {suddenDeathTraces and neutral' = neutral} for 2 Int for Ls is sat
  -- translate: 0.3s, solve: <0.1s
  -- you can move 1 neutral piece in the sudden death variant
  // suddenDeathOneNeutralMove: {suddenDeathTraces and lone neutral' - neutral} for 2 Int for Ls is sat
  -- translate: 0.3s, solve: <0.1s
  -- you can move 2 neutral pieces in the sudden death variant
  // suddenDeathTwoNeutralMoves: {suddenDeathTraces and twoNeutral} for 2 Int for Ls is sat
  -- translate: 1.2s, solve: 0.3s
  -- in the sudden death variant, you still can't win on the first turn
  // suddenDeathNoWinOneTurn: {suddenDeathTraces implies next_state canMove} for 2 Int for Ls is theorem
}


---- Run Statements ----

-- trace with a winner
-- generation time: 0.4s
run {traces and eventually doNothing} for 2 Int for Ls

-- infinite loop trace (no winner)
-- generation time: 0.4s
// run {traces and always canMove} for 2 Int for Ls

-- trace with a winner and at least 5 moves
-- generation time: 2.3s
// run {traces and next_state next_state next_state next_state canMove and eventually doNothing} for 2 Int for Ls

-- infinite loop trace, never loops back to first state
-- generation time: 0.8s
//run {traces and always canMove and next_state (always not init)} for 2 Int for Ls

-- sudden death trace with a winner
-- generation time: 0.3s
// run {suddenDeathTraces and eventually doNothing} for 2 Int for Ls

-- sudden death infinite loop trace (no winner)
-- generation time: 0.4s
// run {suddenDeathTraces and always canMove} for 2 Int for Ls
