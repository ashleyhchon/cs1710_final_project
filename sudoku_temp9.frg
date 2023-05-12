#lang forge

option problem_type temporal
option solver Glucose

one sig BoardState {
    var board: pfunc Int -> Int -> Int
}


pred wellformed {
    all s: BoardState |
        all i: Int | (i <- 0 or i > 9) implies {
            no s.board[i]
            no s.board[Int][i]
            no s.board.i
        }
}

pred init {
  wellformed
  #BoardState.board = 7
}

inst optimizer {
    // StartingState = `PuzzleState0
    // MiddleState = `MiddleState0
    // SolvedState = `SolvedState0
    // BoardState = StartingState + MiddleState + SolvedState
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

pred fill[s: BoardState] {
    all r: values | s.board[r][Int] = values
    all c: values | s.board[Int][c] = values

    all subgrid: values | 
        get_grid[s, subgrid] = values

    // get a cell in the board
    
}

pred solve {
    // StartingState.board in SolvedState.board
    // StartingState.board in MiddleState.board
    // MiddleState.board in SolvedState.board
    // solution[SolvedState]

    BoardState.board in BoardState.board'
    // fill[BoardState.board']
    // middleHalfSolution[MiddleState]
}

pred doNothing {
    BoardState.board = BoardState.board'
}


pred traces {
    init
    always { solve or doNothing }
} 


// run {
//     wellformed
//     solve
//     #StartingState.board = 7 // 7 pre-populated cells
// } for 3 BoardState, 5 Int for optimizer

test expect {
    -- Vacuity test, validate that we can generate some trace. 
    tracesSAT: {traces} for exactly 3 BoardState, 5 Int for optimizer
      is sat
}
run { traces } for exactly 3 BoardState, 5 Int for optimizer