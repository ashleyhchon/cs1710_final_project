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
    all i: Int | (i <= 0 or i > 4) implies {
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
    // Board.board in Board.board'
    // #Board.board' = add[#Board.board, 1]

    some r, c, n: values | Board.board' = Board.board + (r->c->n)
}

pred win {
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

// option logtranslation 1
// option coregranularity 1
// option solver MiniSatProver
// option core_minimization rce
run {traces[5] eventually win} for 5 Int for optimizer


// test expect {
//     tracesSAT: {traces[4]} for 5 Int for optimizer is sat
//     eventuallyWin: {traces[4] and eventually win} for 5 Int for optimizer is sat
//     alreadyWon: {traces[0] and eventually win} for exactly 1 Board, 5 Int for optimizer is sat
//     // emptyStart: {traces[16] and eventually win} for exactly 17 Board, 6 Int for optimizer is sat
// }