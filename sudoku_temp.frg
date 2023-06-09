#lang forge

option problem_type temporal

option solver Glucose

one sig Board {
    var board: pfunc Int -> Int -> Int
}

// fun boardQuadrant(row: Int, col: Int): Int {
//     (row > 1 and col > 1) => 3 else
//     (row > 1 and col <= 1) => 2 else
//     (row <= 1 and col > 1) => 1 else 0
// }

inst optimizer {
    Board = `Board0
    board in Board ->
             (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) -> 
             (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) -> 
             (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9)
}

fun subgrids: set Int -> Int -> Int {
    (1 -> (1 + 2) -> (1 + 2)) +
    (2 -> (1 + 2) -> (3 + 4)) +
    (3 -> (3 + 4) -> (1 + 2)) +
    (4 -> (3 + 4) -> (3 + 4))
}

fun get_grid[subgrid: Int]: set Int {
    let indexes = subgrids[subgrid] |
    let rows = indexes.Int |
    let cols = indexes[Int] |
        Board.board'[rows][cols]
}

fun values: set Int {
    (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9)
}


pred wellformed {
    // all row, col: Int | {
    //     ((row not in values) or (col not in values)) implies
    //     no Board.board[row][col]
    // }

    // -- all entries are between 1-4
    // all row, col: values | {
    //     some Board.board[row][col] => Board.board[row][col] in values
    // }

    // -- if the entry values are the same, they can't be in the same row, column, or quadrant
    // all r1, c1, r2, c2: Int | {
    //     (not (r1 = r2 and c1 = c2) and some Board.board[r1][c1] and some Board.board[r2][c2]) => {
    //         (Board.board[r1][c1] = Board.board[r2][c2]) <=>  --  entry values are the same
    //         ((r1 != r2 and c1 != c2 and boardQuadrant[r1, c1] != boardQuadrant[r2, c2]) and (Board.board[r1][c1] = Board.board[r2][c2]))
    //     }
    // }

    all i: Int | (i <- 0 or i > 9) implies {
        no Board.board[i]
        no Board.board[Int][i]
        no Board.board.i
    }

}

pred init {
    wellformed
    // all disj i, j: Int |
    //     Board.board[i][j] = none or (one Board.board[i][j] and (Board.board[i][j] < 4 or Board.board[i][j] >= 0))

    // #{r, c: values | Board.board[r][c] != none} = 1
    // Board.board[1][1] = 9

    #{r, c: values | Board.board[r][c] = none} = 9

}

// pred move {
//     // some i, j, k: values | {
//     //     Board.board in Board.board'
//     //     #Board.board' = #Board.board + 10
//     // }
//     some r: values | Board.board'[r][Int] = values
//     some c: values | Board.board'[Int][c] = values

//     some subgrid: values | 
//         get_grid[subgrid] = values

//     Board.board in Board.board'
//     #Board.board' = #Board.board + 10
// }

// pred win {
//     // all r: values | {
//     //     all c: values | Board.board[r][c] in values
//     // }
//     some r: values | no Board.board[r][Int] 
//     some c: values | no Board.board[Int][c] 
//     all r: values | Board.board'[r][Int] = values
//     all c: values | Board.board'[Int][c] = values

//     all subgrid: values | 
//         get_grid[subgrid] = values
// }

-- predicate that ensures previous board is one entry away from the next board
pred move {
    Board.board in Board.board'
    #Board.board' = add[#Board.board, 1]
    // some r, c, n: values | Board.board' = Board.board + (r->c->n)
}

pred delete {
    Board.board' in Board.board
    #Board.board' = subtract[#Board.board, 1]
    // some r, c, n: values | Board.board' = Board.board + (r->c->n)
}

-- predicate that checks if the board is solved
pred win {
    Board.board in Board.board'
    all r: values | Board.board'[r][Int] = values
    all c: values | Board.board'[Int][c] = values

    all subgrid: values | 
        get_grid[subgrid] = values

}

pred doNothing {
    Board.board = Board.board'
}

pred traces {
    init
    always { move or doNothing}
}

run {traces and eventually win} for 6 Int for optimizer