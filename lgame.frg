#lang forge

option problem_type temporal
option max_tracelength 10

abstract sig Player {}
one sig Red, Blue extends Player {}

sig Cell {
  r: one Int,
  c: one Int
}

sig L {}

one sig Game {
  Ls: set L -> Cell,
  var red: one L,
  var blue: one L,
  var neutral: set Int -> Int,
  var turn: one Player
}

fun cells[l: one L]: set Int->Int {
  {row, col: Int | (some cell: Game.Ls[l] | cell.r = row and cell.c = col)}
}

// Game board is indexed from -2 to 1 to avoid overflow
pred init {
  -- red L starting position
  cells[Game.red] =
    -2 -> -1 +
    -2 ->  0 +
    -1 ->  0 +
     0 ->  0
  -- blue L starting position
  cells[Game.blue] =
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

    no cells[Game.red] & cells[Game.blue]
    no cells[Game.red] & Game.neutral
    no cells[Game.blue] & Game.neutral
  }
}

pred validMove[l: one L] {
  Game.turn = Red => {
    l != Game.red
    cells[l] in Int->Int - (cells[Game.blue] + Game.neutral)
  } else {
    l != Game.blue
    cells[l] in Int->Int - (cells[Game.red] + Game.neutral)
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

inst CellsAndLs {
  Cell =
    `C00 + `C01 + `C02 + `C03 +
    `C10 + `C11 + `C12 + `C13 +
    `C20 + `C21 + `C22 + `C23 +
    `C30 + `C31 + `C32 + `C33
  r =
    `C00->-2 + `C01->-2 + `C02->-2 + `C03->-2 +
    `C10->-1 + `C11->-1 + `C12->-1 + `C13->-1 +
    `C20-> 0 + `C21-> 0 + `C22-> 0 + `C23-> 0 +
    `C30-> 1 + `C31-> 1 + `C32-> 1 + `C33-> 1
  c =
    `C00->-2 + `C01->-1 + `C02-> 0 + `C03-> 1 +
    `C10->-2 + `C11->-1 + `C12-> 0 + `C13-> 1 +
    `C20->-2 + `C21->-1 + `C22-> 0 + `C23-> 1 +
    `C30->-2 + `C31->-1 + `C32-> 0 + `C33-> 1
  Game = `G
  L = `L00 + `L01 + `L02 + `L03 + `L04 + `L05 + `L06 + `L07 + `L08 + `L09 + `L10 + `L11 + `L12 + `L13 + `L14 + `L15 + `L16 + `L17 + `L18 + `L19 + `L20 + `L21 + `L22 + `L23 + `L24 + `L25 + `L26 + `L27 + `L28 + `L29 + `L30 + `L31 + `L32 + `L33 + `L34 + `L35 + `L36 + `L37 + `L38 + `L39 + `L40 + `L41 + `L42 + `L43 + `L44 + `L45 + `L46 + `L47
  Ls = `G->(
    -- normal Ls
    `L00->(`C00 + `C10 + `C20 + `C21) +
    `L01->(`C01 + `C11 + `C21 + `C22) +
    `L02->(`C02 + `C12 + `C22 + `C23) +
    `L03->(`C10 + `C20 + `C30 + `C31) +
    `L04->(`C11 + `C21 + `C31 + `C32) +
    `L05->(`C12 + `C22 + `C32 + `C33) +
    -- upside-down Ls
    `L06->(`C20 + `C10 + `C00 + `C01) +
    `L07->(`C21 + `C11 + `C01 + `C02) +
    `L08->(`C22 + `C12 + `C02 + `C03) +
    `L09->(`C30 + `C20 + `C10 + `C11) +
    `L10->(`C31 + `C21 + `C11 + `C12) +
    `L11->(`C32 + `C22 + `C12 + `C13) +
    -- backwards Ls
    `L12->(`C01 + `C11 + `C21 + `C20) +
    `L13->(`C02 + `C12 + `C22 + `C21) +
    `L14->(`C03 + `C13 + `C23 + `C22) +
    `L15->(`C11 + `C21 + `C31 + `C30) +
    `L16->(`C12 + `C22 + `C32 + `C31) +
    `L17->(`C13 + `C23 + `C33 + `C32) +
    -- backwards upside-down Ls
    `L18->(`C01 + `C11 + `C21 + `C00) +
    `L19->(`C02 + `C12 + `C22 + `C01) +
    `L20->(`C03 + `C13 + `C23 + `C02) +
    `L21->(`C11 + `C21 + `C31 + `C10) +
    `L22->(`C12 + `C22 + `C32 + `C11) +
    `L23->(`C13 + `C23 + `C33 + `C12) +

    -- everything above transposed
    -- normal Ls
    `L24->(`C00 + `C01 + `C02 + `C12) +
    `L25->(`C10 + `C11 + `C12 + `C22) +
    `L26->(`C20 + `C21 + `C22 + `C32) +
    `L27->(`C01 + `C02 + `C03 + `C13) +
    `L28->(`C11 + `C12 + `C13 + `C23) +
    `L29->(`C21 + `C22 + `C23 + `C33) +
    -- upside-down Ls
    `L30->(`C02 + `C01 + `C00 + `C10) +
    `L31->(`C12 + `C11 + `C10 + `C20) +
    `L32->(`C22 + `C21 + `C20 + `C30) +
    `L33->(`C03 + `C02 + `C01 + `C11) +
    `L34->(`C13 + `C12 + `C11 + `C21) +
    `L35->(`C23 + `C22 + `C21 + `C31) +
    -- backwards Ls
    `L36->(`C10 + `C11 + `C12 + `C02) +
    `L37->(`C20 + `C21 + `C22 + `C12) +
    `L38->(`C30 + `C31 + `C32 + `C22) +
    `L39->(`C11 + `C12 + `C13 + `C03) +
    `L40->(`C21 + `C22 + `C23 + `C13) +
    `L41->(`C31 + `C32 + `C33 + `C23) +
    -- backwards upside-down Ls
    `L42->(`C10 + `C11 + `C12 + `C00) +
    `L43->(`C20 + `C21 + `C22 + `C10) +
    `L44->(`C30 + `C31 + `C32 + `C20) +
    `L45->(`C11 + `C12 + `C13 + `C01) +
    `L46->(`C21 + `C22 + `C23 + `C11) +
    `L47->(`C31 + `C32 + `C33 + `C21)
  )
}


-- CellsandLs Tests
test expect {
  -- translate: <0.1s, solve: <0.1s
  // allCells: {
  //   all row, col: Int | one cell: Cell | cell.r = row and cell.c = col
  // } for 2 Int for CellsAndLs is sat

  -- translate: 3.2s, solve: <0.1s
  // allLs: {
  //   all cell1, cell2, cell3, cell4: Cell | {
  //     isLShape[cell1.r, cell1.c, cell2.r, cell2.c, cell3.r, cell3.c, cell4.r, cell4.c] => {
  //       one l: L | Game.Ls[l] = cell1 + cell2 + cell3 + cell4
  //     }
  //   }
  // } for 2 Int for CellsAndLs is sat
}


-- Standard Game Tests 
test expect {
  -- translate: 0.7s, solve: <0.1s
  // vacuity: {traces} for 2 Int for CellsAndLs is sat
  -- the game can end (there can be a winner)
  -- translate: 0.8s, solve: <0.1s
  // canEndGame: {traces and eventually doNothing} for 2 Int for CellsAndLs is sat
  -- the game can never end
  -- translate: 1s, solve: <0.1s
  // canPlayInfinite: {traces and always canMove} for 2 Int for CellsAndLs is sat
  -- a player can choose to move no neutral piece
  -- translate: 1s, solve: <0.1s
  // noNeutralMoveVacuity: {traces noNeutralMoves} for 2 Int for CellsAndLs is sat
  -- there can't be a winner without a neutral piece being moved
  -- translate: 3s, solve: 1.3s
  // noWinUnlessNeutralMove: {(traces and noNeutralMoves) implies always canMove} for 2 Int for CellsAndLs is theorem
  -- can't win on the first turn
  -- translate: 3.4s, solve: <0.1s
  // noWinOneTurn: {traces implies next_state canMove} for 2 Int for CellsAndLs is theorem
  -- can win in two turns
  -- translate: 0.9s, solve: <0.1s
  // canWinTwoTurns: {traces and next_state next_state (some p: Player | isWinner[p])} for 2 Int for CellsAndLs is sat
  -- red can win
  -- translate: 1s, solve: 0.2s
  // redCanWin: {traces and eventually isWinner[Red]} for 2 Int for CellsAndLs is sat
  -- blue can win
  -- translate: 0.8s, solve: <0.1s
  // blueCanWin: {traces and eventually isWinner[Blue]} for 2 Int for CellsAndLs is sat
  -- if the game is not over, no one can move twice in a row
  -- translate: 2.8s, solve: 26.3s
  // sameTurnNotGameOver: {traces implies always (canMove => turn' != turn)} for 2 Int for CellsAndLs is theorem
  -- once the game ends (nobody takes a move during that turn) the game is permanently over (no further moves will be taken)
  -- translate: 2.7s, solve: 291s
  // permanentlyOver: {traces implies always (doNothing implies always doNothing)} for 2 Int for CellsAndLs is theorem
}


-- Sudden Death Variant Tests
test expect {
  -- translate: 0.9s, solve: 0.2s
  // suddenDeathVacuity: {suddenDeathTraces} for 2 Int for CellsAndLs is sat
  -- translate: 0.7s, solve: <0.1s
  // suddenDeathNoNeutralMoves: {suddenDeathTraces and neutral' = neutral} for 2 Int for CellsAndLs is sat
  -- translate: 0.8s, solve: <0.1s
  // suddenDeathOneNeutralMove: {suddenDeathTraces and lone neutral' - neutral} for 2 Int for CellsAndLs is sat
  -- translate: 0.7s, solve: <0.1s
  // suddenDeathTwoNeutralMoves: {suddenDeathTraces and twoNeutral} for 2 Int for CellsAndLs is sat
  -- translate: 2.8s, solve: 0.3s
  // suddenDeathNoWinOneTurn: {suddenDeathTraces implies next_state canMove} for 2 Int for CellsAndLs is theorem
}


---- Run Statements ----

-- trace with a winner
-- generation time: 1s
run {traces and eventually doNothing} for 2 Int for CellsAndLs

-- infinite loop trace (no winner)
-- generation time: 1s
// run {traces and always canMove} for 2 Int for CellsAndLs

-- trace with a winner and at least 5 moves
-- generation time: 3.4s
// run {traces and next_state next_state next_state next_state canMove and eventually doNothing} for 2 Int for CellsAndLs

-- infinite loop trace, never loops back to first state
-- generation time: 1.5s
// run {traces and always canMove and next_state (always not init)} for 2 Int for CellsAndLs

-- sudden death trace with a winner
-- generation time: 1s
// run {suddenDeathTraces and eventually doNothing} for 2 Int for CellsAndLs

-- infinite loop sudden death trace (no winner)
-- generation time: 1.5s
// run {suddenDeathTraces and always canMove} for 2 Int for CellsAndLs