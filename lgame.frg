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
  Game.red =
     1 -> -1 +
     1 ->  0 +
     0 ->  0 +
    -1 ->  0
  Game.blue =
    -2 ->  0 +
    -2 -> -1 +
    -1 -> -1 +
     0 -> -1
  Game.neutral =
     1 -> -2 +
    -2 ->  1
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

pred doNothing {
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
      some r1, c1, r2, c2, r3, c3, r4, c4: Int |
        trans[r1, c1, r2, c2, r3, c3, r4, c4]
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
  vacuity: {traces} for 2 Int is sat
  canEndGame: {traces implies eventually doNothing} for 2 Int is sat
  canPlayInfinite: {traces implies always canMove} for 2 Int is sat
  noWinUnlessNeutralMove: {(traces and noNeutralMoves) implies always canMove} for 2 Int is theorem
  noWinOneTurn: {traces implies next_state canMove} for 2 Int is theorem
}

run { traces } for 2 Int
