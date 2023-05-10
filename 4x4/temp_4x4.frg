#lang forge

option problem_type temporal

option solver Glucose

-- sig for the sudoku board
one sig Board {
    var board: pfunc Int -> Int -> Int
}

-- optimizer to make the solver run faster
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

-- function to restrict values in board to 1-4
fun values: set Int {
    (1 + 2 + 3 + 4)
}

-- predicate to check that board stays within the bounds of 1-4
pred wellformed {
    all i: Int | (i <= 0 or i > 4) implies {
        no Board.board[i]
        no Board.board[Int][i]
        no Board.board.i
    }

}

-- predicate to check that the board is initizalized with the "empty" number of empty cells
pred init[empty: Int] {
    wellformed

    #{r, c: values | Board.board[r][c] = none} = empty
}

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

-- predicate that checks whether the previous board is the same as the next board
pred doNothing {
    Board.board' = Board.board
}

-- traces predicate
pred traces[empty: Int] {
    init[empty]
    always {move or doNothing}
}

-- predicates for testing

pred initWrong {
    wellformed

    // #{r, c: values | Board.board[r][c] = none} = empty
    Board.board[1][1] = 1
    Board.board[2][2] = 1
}

pred initHardCoded {
    wellformed

    // #{r, c: values | Board.board[r][c] = none} = empty
    Board.board[1][1] = 1
}
pred tracesMistake {
    initWrong
    always {move or doNothing}
}

pred tracesWithRemove {
    initWrong
    always {move or doNothing or delete}
}

pred outOfBounds {
    not wellformed
}
pred tracesOutOfBounds {
    outOfBounds
    always {move or doNothing}
}

// don't know how to check all future states
pred staysFilled { 
    always {
        all r, c: values | {
            some Board.board[r][c] => Board.board'[r][c] = Board.board[r][c]
        }
    }
}


// option logtranslation 1
// option coregranularity 1
// option solver MiniSatProver
// option core_minimization rce
// run {traces[5] eventually win} for 5 Int for optimizer


test expect {
    -- vacuity test
    tracesSAT: {traces[4]} for 5 Int for optimizer is sat
    -- tests that the board eventually gets solved
    eventuallyWin: {traces[4] and eventually win} for 5 Int for optimizer is sat
    -- tests that a full board is always in the win state
    alreadyWon: {traces[0] and always win} for exactly 1 Board, 5 Int for optimizer is sat
    -- tests that a board with incorrectly filled starting values is never in the win state
    incorrectStart: {tracesMistake and eventually win} for 5 Int for optimizer is unsat
    -- tests that a board with out of bounds values is never in the win state
    outOfBounds: {tracesOutOfBounds and eventually win} for 5 Int for optimizer is unsat
    -- tests that a board with incorrectly filled starting values is always in a losing (not won) state
    invalidNeverWins: {tracesMistake and always not win} for 5 Int for optimizer is sat
    -- tests that filled values stay the same in the next state
    sameCells: {traces[4] and staysFilled} for 5 Int for optimizer is sat
    -- tests that a board with incorrectly filled starting values can be corrected and eventually solved
    correctsMistake: {tracesWithRemove and eventually win} for 5 Int for optimizer is sat

    -- we weren't able to test this but we wanted to check that we could solve a completely empty board
    // emptyStart: {traces[16] and eventually win} for exactly 17 Board, 6 Int for optimizer is sat
}