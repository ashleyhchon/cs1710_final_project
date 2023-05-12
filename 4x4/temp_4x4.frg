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

-- helper function to get the subgrids of the board
fun subgrids: set Int -> Int -> Int {
    (1 -> (1 + 2) -> (1 + 2)) +
    (2 -> (1 + 2) -> (3 + 4)) +
    (3 -> (3 + 4) -> (1 + 2)) +
    (4 -> (3 + 4) -> (3 + 4))
}

-- returns values in a subgrid
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
    all i: Int | (i < 1 or i > 4) implies {
        no Board.board[i]
        no Board.board[Int][i]
        no Board.board.i
    }

}

-- predicate to check that the board is initizalized with the "empty" number of empty cells. empty cannot be greater than 4 because of technical issues...
pred init[empty: Int] {
    wellformed

    #{r, c: values | Board.board[r][c] = none} = empty

}

-- predicate that ensures previous board is one entry away from the next board
pred move {
    Board.board in Board.board'
    #Board.board' = add[#Board.board, 1]
    -- a suggestion from Tim but it was unsat and took too long :(
    // some r, c, n: values | Board.board' = Board.board + (r->c->n)
    one r, c: values | {
        Board.board[r][c] != Board.board'[r][c]
    }
}

-- predicate that allows the next state to subtract a cell, but checks that no other cells have changed values
pred delete {
    Board.board' in Board.board
    #Board.board' = subtract[#Board.board, 1]
    one r, c: values | {
        Board.board[r][c] != Board.board'[r][c]
    }
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


-------------------------- predicates for testing

-- separate init for an incorrect starting board (used for tests)
pred initWrong[empty: Int] {
    wellformed

    #{r, c: values | Board.board[r][c] = none} = empty
    Board.board[1][1] = 1
    Board.board[2][2] = 1
}

pred initWrongMult[empty: Int] {
    wellformed

     #{r, c: values | Board.board[r][c] = none} = empty
    Board.board[1][1] = 1
    Board.board[1][2] = 1
    Board.board[2][2] = 1
}

-- hardcoded start board with no mistakes (cannot ensure that only value is filled becuase we are unable to check all empty cells)
pred initHardCoded {
    wellformed

    // #{r, c: values | Board.board[r][c] = none} = empty
    Board.board[1][1] = 1
}

-- running a trace with an incorrect starting board and 2 empty spaces
pred tracesMistake {
    initWrong[2]
    always {move or doNothing}
}

-- a trace with an incorrect starting board but with the option to fix the mistake
pred tracesWithRemove[empty: Int] {
    initWrong[empty]
    always {move or doNothing or delete}
}

pred tracesWithRemoveMult[empty: Int] {
    initWrongMult[empty]
    always {move or doNothing or delete}
}

-- tried hardcoding states to check if there is an incorrect start board with one space and only one move left, you cannot win
// pred tracesLimitedMoves {
//     initWrong[1]
//     next_state move
//     next_state next_state win
// }

-- making an invalid board
pred outOfBounds {
    not wellformed
}

-- running a trace with an invalid board
pred tracesOutOfBounds {
    outOfBounds
    always {move or doNothing}
}

// checking that any filled cell should stay filled with the same value
pred staysFilled { 
    always {
        all r, c: values | {
            some Board.board[r][c] => Board.board'[r][c] = Board.board[r][c]
        }
    }
}

-- played around with this during Tim's office hours
// option logtranslation 1
// option coregranularity 1
// option solver MiniSatProver
// option core_minimization rce

-- cannot run this with more than 4 empty spaces despite experimenting with diffirent Int values.
// run {traces[5] eventually win} for 5 Int for optimizer

-- working ex
run {traces[4] eventually win} for 5 Int for optimizer

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
    correctsMistake: {tracesWithRemove[2] and eventually win} for 5 Int for optimizer is sat
    -- tests that a filled board with a mistake can be corrected
    correctsFilledMistake: {tracesWithRemove[0] and eventually win} for 5 Int for optimizer is sat
    -- uses our staysFilled predicate to ensure that some cell has been deleted
    somethingGetsRemoved: {tracesWithRemove[2] and eventually win and staysFilled} for 5 Int for optimizer is unsat


    -- tests that even with more than one mistake, the board can be corrected. We observed that this actually creates boards with many mistakes and it cannot eventually win.
    // correctsMistakeMult: {tracesWithRemoveMult[2] and eventually win} for 5 Int for optimizer is sat

    -- we wanted to test that a board with a mistake and one move left cannot be won. however we had difficulties testing trace length and saw weird behavior when we hardcoded next states
    // correctsMistakeOne: {tracesLimitedMoves } for 5 Int for optimizer is unsat

    -- we weren't able to test this but we wanted to check that we could solve a completely empty board
    // emptyStart: {traces[16] and eventually win} for exactly 17 Board, 6 Int for optimizer is sat
}

// run {tracesWithRemove[1] and eventually win} for 5 Int for optimizer
// run {tracesWithRemoveMult[1] and eventually win} for 5 Int for optimizer