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

pred isLShape[r1, c1, r2, c2, r3, c3, r4, c4: Int] {
  {
    r1 = r2
    adjacent[c1, c2]
    r2 = r3
    adjacent[c2, c3]
    c3 = c4
    adjacent[r3, r4]
  } or {
    c1 = c2
    adjacent[r1, r2]
    c2 = c3
    adjacent[r2, r3]
    r3 = r4
    adjacent[c3, c4]
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

pred transEnabled[L: set Int -> Int] {
  Game.turn = Red => {
    L != Game.red
    L in Int->Int - Game.(blue + neutral)
  } else {
    L != Game.blue
    L in Int->Int - Game.(red + neutral)
  }
}

pred trans[L: set Int -> Int] {
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

pred doNothing {
  red' = red
  blue' = blue
  neutral' = neutral
  turn' = turn
}

pred traces {
  init
  always {
    some r1, c1, r2, c2, r3, c3, r4, c4: Int | {
      isLShape[r1, c1, r2, c2, r3, c3, r4, c4]
      let L = r1->c1 + r2->c2 + r3->c3 + r4->c4 | {
        #L = 4
        transEnabled[L]
        trans[L]
      }
    } or {
      no r1, c1, r2, c2, r3, c3, r4, c4: Int | {
        isLShape[r1, c1, r2, c2, r3, c3, r4, c4]
        let L = r1->c1 + r2->c2 + r3->c3 + r4->c4 | {
          #L = 4
          transEnabled[L]
        }
      }
      doNothing
    }
  }
}

run { wellFormed traces } for 2 Int
