#lang forge
open "sudoku.frg"


test expect {
    {subgrids[1] = (1 + 2 + 3) -> (1 + 2 + 3)} is sat
    {subgrids[1][1] = (1 + 2 + 3)} is sat
    {subgrids[4] = (4 + 5 + 6) -> (1 + 2 + 3)} is sat
    {subgrids[4][6] = (1 + 2 + 3)} is sat
}

pred noHigher {
    all s: BoardState |
    all i: Int | (i > 9) implies {
        no s.board[i]
        no s.board[Int][i]
        no s.board.i
    }
}

pred noLower {
    all s: BoardState |
    all i: Int | i <- 0 implies {
        no s.board[i]
        no s.board[Int][i]
        no s.board.i
    }
}


test suite for wellformed {
    assert noLower is necessary for wellformed
    assert noLower is necessary for wellformed

    // example fullBoard1 is {wellformed} for {
    //     BoardState = `StartingState0 + `MiddleState0 + `SolvedState0
    //     StartingState = `StartingState0
    //     MiddleState = `MiddleState0
    //     SolvedState = `SolvedState0
    //     board = `StartingState0 -> ((1 -> 1 -> 1) +
    //                                 (1 -> 2 -> 2) +
    //                                 (1 -> 3 -> 3)) +
    //             `MiddleState0 -> ((1 -> 1 -> 1) +
    //                                 (1 -> 2 -> 2) +
    //                                 (1 -> 3 -> 3)) +
    //             `SolvedState0 -> ((1 -> 1 -> 1) +
    //                                 (1 -> 2 -> 2) +
    //                                 (1 -> 3 -> 3)) 

        
        
         // + `MiddleState0 -> (1 -> 1 -> 1) + `SolvedState0 -> (1 -> 1 -> 1)
    // }

}

pred allEntryInValues[s: BoardState] {
    all r: values | {
        all c: values | s.board[r][c] in values
    }
}

test suite for solution {
    assert allEntryInValues is necessary for solution
}


// test suite for solution {
//     example completed is {some b: BoardState | solution[b]} for {
//         BoardState = `StartingState0 + `MiddleState0 + `SolvedState0 
//         StartingState = `StartingState0
//         MiddleState = `MiddleState0
//         SolvedState = `SolvedState0
//         board = `SolvedState0 -> (1 -> 1 -> 6 +
//                                   1 -> 2 -> 8 +
//                                   1 -> 3 -> 9 +
//                                   1 -> 4 -> 7 +
//                                   1 -> 5 -> 4 +
//                                   1 -> 6 -> 3 + 
//                                   1 -> 7 -> 5 + 
//                                   1 -> 8 -> 1 +
//                                   1 -> 9 -> 2 +
//                                   2 -> 1 -> 2 +
//                                   2 -> 2 -> 5 +
//                                   2 -> 3 -> 3 +
//                                   2 -> 4 -> 6 +
//                                   2 -> 5 -> 9 +
//                                   2 -> 6 -> 1 + 
//                                   2 -> 7 -> 7 + 
//                                   2 -> 8 -> 4 +
//                                   2 -> 9 -> 8 +
//                                   3 -> 1 -> 1 +
//                                   3 -> 2 -> 4 +
//                                   3 -> 3 -> 7 +
//                                   3 -> 4 -> 5 +
//                                   3 -> 5 -> 2 +
//                                   3 -> 6 -> 8 + 
//                                   3 -> 7 -> 6 + 
//                                   3 -> 8 -> 3 +
//                                   3 -> 9 -> 9 +
//                                   4 -> 1 -> 8 +
//                                   4 -> 2 -> 2 +
//                                   4 -> 3 -> 6 +
//                                   4 -> 4 -> 3 +
//                                   4 -> 5 -> 1 +
//                                   4 -> 6 -> 7 + 
//                                   4 -> 7 -> 9 + 
//                                   4 -> 8 -> 5 +
//                                   4 -> 9 -> 4 +
//                                   5 -> 1 -> 5 +
//                                   5 -> 2 -> 3 +
//                                   5 -> 3 -> 4 +
//                                   5 -> 4 -> 2 +
//                                   5 -> 5 -> 8 +
//                                   5 -> 6 -> 9 + 
//                                   5 -> 7 -> 1 + 
//                                   5 -> 8 -> 6 +
//                                   5 -> 9 -> 7 +
//                                   6 -> 1 -> 9 +
//                                   6 -> 2 -> 7 +
//                                   6 -> 3 -> 1 +
//                                   6 -> 4 -> 4 +
//                                   6 -> 5 -> 5 +
//                                   6 -> 6 -> 6 + 
//                                   6 -> 7 -> 8 + 
//                                   6 -> 8 -> 2 +
//                                   6 -> 9 -> 3 +
//                                   7 -> 1 -> 7 +
//                                   7 -> 2 -> 1 +
//                                   7 -> 3 -> 2 +
//                                   7 -> 4 -> 8 +
//                                   7 -> 5 -> 3 +
//                                   7 -> 6 -> 5 + 
//                                   7 -> 7 -> 4 + 
//                                   7 -> 8 -> 9 +
//                                   7 -> 9 -> 6 +
//                                   8 -> 1 -> 4 +
//                                   8 -> 2 -> 6 +
//                                   8 -> 3 -> 5 +
//                                   8 -> 4 -> 9 +
//                                   8 -> 5 -> 7 +
//                                   8 -> 6 -> 2 + 
//                                   8 -> 7 -> 3 + 
//                                   8 -> 8 -> 8 +
//                                   8 -> 9 -> 1 +
//                                   9 -> 1 -> 3 +
//                                   9 -> 2 -> 9 +
//                                   9 -> 3 -> 8 +
//                                   9 -> 4 -> 1 +
//                                   9 -> 5 -> 6 +
//                                   9 -> 6 -> 4 + 
//                                   9 -> 7 -> 2 + 
//                                   9 -> 8 -> 7 +
//                                   9 -> 9 -> 5) 
//     }
// }


    

