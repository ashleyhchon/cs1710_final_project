#lang forge

abstract sig BoardState {
    board: pfunc Int -> Int -> Int
}

// ideally would be one instead of lone, but we had it be 
// purely for testing purposes. 
lone sig StartingState extends BoardState {}
lone sig MiddleState extends BoardState {}
lone sig SolvedState extends BoardState {}

pred wellformed {
    all s: BoardState |
        all i: Int | (i < 1 or i > 9) implies {
            no s.board[i]
            no s.board[Int][i]
            no s.board.i
        }
}

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

fun values: set Int {
    (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9)
}

fun get_grid[s: BoardState, subgrid: Int]: set Int {
    let indexes = subgrids[subgrid] |
    let rows = indexes.Int |
    let cols = indexes[Int] |
        s.board[rows][cols]
}

pred solution[s: StartingState] {
    all r: values | s.board[r][Int] = values
    all c: values | s.board[Int][c] = values

    all subgrid: values | 
        get_grid[s, subgrid] = values
}

pred middleSolution[s: StartingState] {
    some r: values | s.board[r][Int] = values
    some c: values | s.board[Int][c] = values

    some subgrid: values | {
        get_grid[s, subgrid] = values
    }
    
    #s.board = 9
}

pred middleHalfSolution[s: StartingState] {
    some r: values | s.board[r][Int] = values
    some c: values | s.board[Int][c] = values

    some subgrid: values | {
        get_grid[s, subgrid] = values
    }

}

pred solve {
    StartingState.board in SolvedState.board
    StartingState.board in MiddleState.board
    MiddleState.board in SolvedState.board
    solution[SolvedState]
    middleHalfSolution[MiddleState]
}


run {
    wellformed
    solve
    #StartingState.board = 7 // 7 pre-populated cells
} for 3 BoardState, 5 Int for optimizer


