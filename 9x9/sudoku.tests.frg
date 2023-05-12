#lang forge
open "sudoku.frg"

test expect {
    -- testing that we can index into the board correctly with our helper function
    {subgrids[1] = (1 + 2 + 3) -> (1 + 2 + 3)} is sat
    {subgrids[1][1] = (1 + 2 + 3)} is sat
    {subgrids[4] = (4 + 5 + 6) -> (1 + 2 + 3)} is sat
    {subgrids[4][6] = (1 + 2 + 3)} is sat
}

-- testing the upper bound of wellformed
pred noHigher {
    all s: BoardState |
    all i: Int | (i > 9) implies {
        no s.board[i]
        no s.board[Int][i]
        no s.board.i
    }
}

-- testing lower bound of wellformed
pred noLower {
    all s: BoardState |
    all i: Int | i <- 0 implies {
        no s.board[i]
        no s.board[Int][i]
        no s.board.i
    }
}


test suite for wellformed {
    -- check bounds
    assert noHigher is necessary for wellformed
    assert noLower is necessary for wellformed

    -- check that the cells are contained from 0-9
    example justInner is {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (1 -> 1 -> 1 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- check that wellformed is unsat if you have a row/value/grid > 9
    example rowsMoreThan9 is not {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (10 -> 1 -> 1 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- tests lower bound of rows
    example rowsLessThan1 is not {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (0 -> 1 -> 1 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- tests upper bound of columns
    example colsMoreThan9 is not {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (1 -> 10 -> 1 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- tests lower bound of columns
    example colsLessThan1 is not {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (1 -> 0 -> 1 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- tests for valid values in the cells
    example valuesMoreThan9 is not {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (1 -> 1 -> 10 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- checks lower bound of values
    example valuesLessThan1 is not {wellformed} for {
        BoardState = `StartingState0
        #Int = 5
        board = `StartingState0 -> (1 -> 1 -> 0 +
                                    1 -> 2 -> 2 +
                                    1 -> 3 -> 3) 
    }

    -- making sure a full 9x9 is valid
    example FullBoard is {wellformed} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5) 
    }

}

test suite for middleHalfSolution {
    -- tests that a valid half solution has at least one full row, one full column and one full grid
    example oneRowColGrid is {some b: StartingState | middleHalfSolution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  4 -> 1 -> 8 +
                                  5 -> 1 -> 5 +
                                  6 -> 1 -> 9 +
                                  7 -> 1 -> 7 +
                                  8 -> 1 -> 4 +
                                  9 -> 1 -> 3) 
    }
    -- tests an instance that is not full enough to be a middle solution
    example noFullCol is not {some b: StartingState | middleHalfSolution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  4 -> 1 -> 8 +
                                  5 -> 1 -> 5 +
                                  6 -> 1 -> 9 +
                                  7 -> 1 -> 7 +
                                  8 -> 1 -> 4) 
    }
    -- tests that without a full subgrid, we cannot have a middle half solution
    example noFullGrid is not {some b: StartingState | middleHalfSolution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  4 -> 1 -> 8 +
                                  5 -> 1 -> 5 +
                                  6 -> 1 -> 9 +
                                  7 -> 1 -> 7 +
                                  8 -> 1 -> 4 +
                                  9 -> 1 -> 3) 
    }
    -- tests that without a full row, we cannot have a middle half solution
    example noFullRow is not {some b: StartingState | middleHalfSolution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  4 -> 1 -> 8 +
                                  5 -> 1 -> 5 +
                                  6 -> 1 -> 9 +
                                  7 -> 1 -> 7 +
                                  8 -> 1 -> 4 +
                                  9 -> 1 -> 3) 
    }
    -- a full board should count as a middle solution 
    example fullBoard is {some b: StartingState | middleHalfSolution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5) 
    }
}

test suite for solution {
    -- vacuity check
    test expect {
        {some b: BoardState | solution[b]} is sat
        {some b: BoardState | not solution[b]} is sat
    }

    -- tests that a full hardcoded board is a solution
    example completed is {some b: StartingState | solution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5) 
    }

    -- checks a full board with a mistake
    example oneMistake is not {some b: StartingState | solution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 1 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5) 
    }

    -- checks a board that is missing a value
    example missingCell is not {some b: StartingState | solution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5) 
    }
    -- checks the structure of the board must still hold for a valid solution
    example outofBound is not {some b: StartingState | solution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 0 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5) 
    }

    -- even with a full board, an invalid index shouuld not be a solution
    example extraOutOfBound is {some b: StartingState | solution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5 +
                                  0 -> 0 -> 1) 
    }
    -- checking for a valid board structure again
    example extraOutOfBoundWithNonValue is not {some b: StartingState | solution[b]} for {
        BoardState = `SolvedState0
        #Int = 5
        board = `SolvedState0 -> (1 -> 1 -> 6 +
                                  1 -> 2 -> 8 +
                                  1 -> 3 -> 9 +
                                  1 -> 4 -> 7 +
                                  1 -> 5 -> 4 +
                                  1 -> 6 -> 3 + 
                                  1 -> 7 -> 5 + 
                                  1 -> 8 -> 1 +
                                  1 -> 9 -> 2 +
                                  2 -> 1 -> 2 +
                                  2 -> 2 -> 5 +
                                  2 -> 3 -> 3 +
                                  2 -> 4 -> 6 +
                                  2 -> 5 -> 9 +
                                  2 -> 6 -> 1 + 
                                  2 -> 7 -> 7 + 
                                  2 -> 8 -> 4 +
                                  2 -> 9 -> 8 +
                                  3 -> 1 -> 1 +
                                  3 -> 2 -> 4 +
                                  3 -> 3 -> 7 +
                                  3 -> 4 -> 5 +
                                  3 -> 5 -> 2 +
                                  3 -> 6 -> 8 + 
                                  3 -> 7 -> 6 + 
                                  3 -> 8 -> 3 +
                                  3 -> 9 -> 9 +
                                  4 -> 1 -> 8 +
                                  4 -> 2 -> 2 +
                                  4 -> 3 -> 6 +
                                  4 -> 4 -> 3 +
                                  4 -> 5 -> 1 +
                                  4 -> 6 -> 7 + 
                                  4 -> 7 -> 9 + 
                                  4 -> 8 -> 5 +
                                  4 -> 9 -> 4 +
                                  5 -> 1 -> 5 +
                                  5 -> 2 -> 3 +
                                  5 -> 3 -> 4 +
                                  5 -> 4 -> 2 +
                                  5 -> 5 -> 8 +
                                  5 -> 6 -> 9 + 
                                  5 -> 7 -> 1 + 
                                  5 -> 8 -> 6 +
                                  5 -> 9 -> 7 +
                                  6 -> 1 -> 9 +
                                  6 -> 2 -> 7 +
                                  6 -> 3 -> 1 +
                                  6 -> 4 -> 4 +
                                  6 -> 5 -> 5 +
                                  6 -> 6 -> 6 + 
                                  6 -> 7 -> 8 + 
                                  6 -> 8 -> 2 +
                                  6 -> 9 -> 3 +
                                  7 -> 1 -> 7 +
                                  7 -> 2 -> 1 +
                                  7 -> 3 -> 2 +
                                  7 -> 4 -> 8 +
                                  7 -> 5 -> 3 +
                                  7 -> 6 -> 5 + 
                                  7 -> 7 -> 4 + 
                                  7 -> 8 -> 9 +
                                  7 -> 9 -> 6 +
                                  8 -> 1 -> 4 +
                                  8 -> 2 -> 6 +
                                  8 -> 3 -> 5 +
                                  8 -> 4 -> 9 +
                                  8 -> 5 -> 7 +
                                  8 -> 6 -> 2 + 
                                  8 -> 7 -> 3 + 
                                  8 -> 8 -> 8 +
                                  8 -> 9 -> 1 +
                                  9 -> 1 -> 3 +
                                  9 -> 2 -> 9 +
                                  9 -> 3 -> 8 +
                                  9 -> 4 -> 1 +
                                  9 -> 5 -> 6 +
                                  9 -> 6 -> 4 + 
                                  9 -> 7 -> 2 + 
                                  9 -> 8 -> 7 +
                                  9 -> 9 -> 5 +
                                  0 -> 0 -> 0) 
    }

}