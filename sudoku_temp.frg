#lang forge

option problem_type temporal

option solver Glucose

one sig Board {
    var board: pfunc Int -> Int -> Int
}

fun boardQuadrant(row: Int, col: Int): Int {
    (row > 1 and col > 1) => 3 else
    (row > 1 and col <= 1) => 2 else
    (row <= 1 and col > 1) => 1 else 0
}

fun values: set Int {
    (0 + 1 + 2 + 3)
}

pred wellformed {
    all row, col: Int | {
        (row < 0 or row > 3 or col < 0 or col > 3) implies
        no Board.board[row][col]
    }

    -- all entries are between 1-4
    all row, col: values | {
        some Board.board[row][col] => Board.board[row][col] in values
    }

    -- if the entry values are the same, they can't be in the same row, column, or quadrant
    all r1, c1, r2, c2: Int | {
        (not (r1 = r2 and c1 = c2) and some Board.board[r1][c1] and some Board.board[r2][c2]) => {
            (Board.board[r1][c1] = Board.board[r2][c2]) <=>  --  entry values are the same
            ((r1 != r2 and c1 != c2 and boardQuadrant[r1, c1] != boardQuadrant[r2, c2]) and (Board.board[r1][c1] = Board.board[r2][c2]))
        }
    }
}

pred init {
    wellformed

    all disj i, j: Int |
        Board.board[i][j] = none or (one Board.board[i][j] and (Board.board[i][j] < 4 or Board.board[i][j] >= 0))

    #Board.board = 3
}

pred move {
    some i, j: Int | {
        no Board.board[i][j]
        some Board.board'[i][j]
    }
}

pred win {
    all r: values | Board.board[r][Int] = values
    all c: values | Board.board[Int][c] = values
}

pred doNothing {
    Board.board = Board.board'
}

pred traces {
    init
    always {move or win or doNothing}
}

run traces