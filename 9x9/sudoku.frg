#lang forge

abstract sig BoardState {
    board: pfunc Int -> Int -> Int
}

// ideally would be one instead of lone, but we had it be 
// purely for testing purposes. 
lone sig StartingState extends BoardState {}
lone sig MiddleState extends BoardState {}
lone sig SolvedState extends BoardState {}

-- basic predicate to constrain the board to be 9x9
pred wellformed {
    all s: BoardState |
        all i: Int | (i < 1 or i > 9) implies {
            no s.board[i]
            no s.board[Int][i]
            no s.board.i
        }
}

-- optimizer to make solver run faster
inst optimizer {
    StartingState = `PuzzleState0
    MiddleState = `MiddleState0
    SolvedState = `SolvedState0
    BoardState = StartingState + MiddleState + SolvedState
    board in BoardState -> 
             (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) -> 
             (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9) -> 
             (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9)
}

-- helper to get the subgrids of a board
fun subgrids: set Int -> Int -> Int {
    (1 -> (1 + 2 + 3) -> (1 + 2 + 3)) +
    (2 -> (1 + 2 + 3) -> (4 + 5 + 6)) +
    (3 -> (1 + 2 + 3) -> (7 + 8 + 9)) +
    (4 -> (4 + 5 + 6) -> (1 + 2 + 3)) +
    (5 -> (4 + 5 + 6) -> (4 + 5 + 6)) +
    (6 -> (4 + 5 + 6) -> (7 + 8 + 9)) +
    (7 -> (7 + 8 + 9) -> (1 + 2 + 3)) +
    (8 -> (7 + 8 + 9) -> (4 + 5 + 6)) +
    (9 -> (7 + 8 + 9) -> (7 + 8 + 9))
}

-- limiting possible values when we refer to r,c and cell values
fun values: set Int {
    (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9)
}

-- returns values in a subgrid
fun get_grid[s: BoardState, subgrid: Int]: set Int {
    let indexes = subgrids[subgrid] |
    let rows = indexes.Int |
    let cols = indexes[Int] |
        s.board[rows][cols]
}

-- checks rows, columns, and grids so that they have values 1-9
pred solution[s: StartingState] {
    all r: values | s.board[r][Int] = values
    all c: values | s.board[Int][c] = values

    all subgrid: values | 
        get_grid[s, subgrid] = values
}

-- shows transition from start state to solution state. no values should change in the transition. Could not specifiy how many new cells were allowed to be filled in this state because of bitwidth issues
pred middleHalfSolution[s: StartingState] {
    some r: values | s.board[r][Int] = values
    some c: values | s.board[Int][c] = values

    some subgrid: values | {
        get_grid[s, subgrid] = values
    }
    -- would have liked to specify how many cells were allowed to be filled in this state, however, we would have also had to constrain the number of empty cells which we could not do becaue of bitwidth issues. Using only the following line leads to inconsistent instances
    // #s.board = 42
}

pred solve {
    StartingState.board in SolvedState.board
    StartingState.board in MiddleState.board
    MiddleState.board in SolvedState.board
    -- this is why we switched to temporal because the middle state was not very useful for understanding the final state / didn't provide any new information
    solution[SolvedState]
    middleHalfSolution[MiddleState]
}


run {
    wellformed
    solve
    #StartingState.board = 7 // 7 pre-populated cells (weird start boards sometimes)
} for 3 BoardState, 5 Int for optimizer


