#lang forge

option problem_type temporal

abstract sig Player {}
one sig Red, Blue extends Player {}

abstract sig Cell {}
one sig Red1, Red2, Red3, Red4, Blue1, Blue2, Blue3, Blue4, N1, N2 extends Cell {}

one sig Game {
  var board: pfunc Int -> Int -> Cell,
  var turn: one Player
}

pred init {
  Game.board[1][-1] = Red1
  Game.board[1][0] = Red2
  Game.board[0][0] = Red3
  Game.board[-1][0] = Red4
  Game.board[-2][0] = Blue1
  Game.board[-2][-1] = Blue2
  Game.board[-1][-1] = Blue3
  Game.board[0][-1] = Blue4
  Game.board[1][-2] = N1
  Game.board[-2][1] = N2
  Game.turn = Red
}

pred adjacent[c1: one Cell, c2: one Cell] {
  some r, c: Int | {
    Game.board[r][c] = c1
    (
      Game.board[subtract[r, 1]][c] = c2 or
      Game.board[r][subtract[c, 1]] = c2 or
      Game.board[add[r, 1]][c] = c2 or
      Game.board[r][add[c, 1]] = c2
    )
  }
}

pred diagonal[c1: one Cell, c2: one Cell] {
  some r, c: Int | {
    Game.board[r][c] = c1
    (
      Game.board[subtract[r, 1]][subtract[c, 1]] = c2 or
      Game.board[subtract[r, 1]][add[c, 1]] = c2 or
      Game.board[add[r, 1]][subtract[c, 1]] = c2 or
      Game.board[add[r, 1]][add[c, 1]] = c2
    )
  }
}

pred wellFormedLPieces {
  always {
    adjacent[Red1, Red2]
    adjacent[Red2, Red3]
    adjacent[Red3, Red4]
    diagonal[Red1, Red3]
    not diagonal[Red2, Red4]

    adjacent[Blue1, Blue2]
    adjacent[Blue2, Blue3]
    adjacent[Blue3, Blue4]
    diagonal[Blue1, Blue3]
    not diagonal[Blue2, Blue4]
  }
}

pred wellFormedBoard {
  always {
    all row, col: Int | {
      (row < -2 or row > 1 or col < -2 or col > 1)
        implies no Game.board[row][col]
    }
    all cell: Cell | one r, c: Int | Game.board[r][c] = cell
  }
}

pred wellFormed {
  wellFormedLPieces
  wellFormedBoard
}

pred transLPiece {
  let red = Red1 + Red2 + Red3 + Red4 |
  let blue = Blue1 + Blue2 + Blue3 + Blue4 |
  Game.turn = Red => {
    Game.board'.red != Game.board.red
    Game.board'.blue = Game.board.blue
  } else {
    Game.board'.blue != Game.board.blue
    Game.board'.red = Game.board.red
  }
  Game.board'.N1 = Game.board.N1
  Game.board'.N2 = Game.board.N2
  Game.turn' != Game.turn
}

pred transNPiece {
  Game.board'.(Cell - N1 - N2) = Game.board.(Cell - N1 - N2)
  Game.board'.N1 = Game.board.N1 or Game.board'.N2 = Game.board.N2
  Game.turn' != Game.turn
}

pred winningState {
   {Game.board'.(Blue1 + Blue2 + Blue3 + Blue4) = Game.board.(Blue1 + Blue2 + Blue3 + Blue4)
    Game.board'.N1 = Game.board.N1
    Game.board'.N2 = Game.board.N2
   } implies Game.board'.(Red1 + Red2 + Red3 + Red4) = Game.board.(Red1 + Red2 + Red3 + Red4)
}

pred doNothing {
  Game.board' = Game.board
  Game.turn' = Game.turn
}

pred traces {
  init
  always {
    transLPiece or doNothing
    // doNothing => not transEnabled
  }
  Game.board' != Game.board
  Game.board'' != Game.board'
}

run { wellFormed traces } for 3 Int
