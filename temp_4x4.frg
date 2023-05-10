#lang forge

option problem_type temporal

option solver Glucose

one sig Board {
    var board: pfunc Int -> Int -> Int
}

inst optimizer {
    Board = `Board0
    board in Board ->
             (1 + 2 + 3 + 4) -> 
             (1 + 2 + 3 + 4) -> 
             (1 + 2 + 3 + 4)
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
    (1 + 2 + 3 + 4)
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

    all i: Int | (i < 1 or i > 4) implies {
        no Board.board[i]
        no Board.board[Int][i]
        no Board.board.i
    }

}

pred init[empty: Int] {
    wellformed

    #{r, c: values | Board.board[r][c] = none} = empty
    
}

pred move {
    // some r: values | Board.board'[r][Int] in values
    // some c: values | Board.board'[Int][c] in values

    // some subgrid: values | 
    //     get_grid[subgrid] in values

    Board.board in Board.board'
    #Board.board' = add[#Board.board, 1]
}

pred win {
    // all r: values | {
    //     all c: values | Board.board[r][c] in values
    // }
    // some r: values | no Board.board[r][Int] 
    // some c: values | no Board.board[Int][c] 
    Board.board in Board.board'
    all r: values | Board.board'[r][Int] = values
    all c: values | Board.board'[Int][c] = values

    all subgrid: values | 
        get_grid[subgrid] = values

}

pred doNothing {
    Board.board' = Board.board
}

pred traces[empty: Int] {
    init[empty]
    always {move or doNothing}
}

// run {traces[4] and eventually win} for 5 Int for optimizer


test expect {
    tracesSAT: {traces[4]} for 5 Int for optimizer is sat
    eventuallyWin: {traces[4] and eventually win} for 5 Int for optimizer is sat
    alreadyWon: {traces[0] and eventually win} for exactly 1 Board, 5 Int for optimizer is sat
    emptyStart: {traces[6] and eventually win} for 6 Int for optimizer is sat
}