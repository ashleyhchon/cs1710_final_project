#lang forge/bsl
open "4x4_sudoku.frg"


test expect {
    {boardQuadrant[1, 2] = 1} is sat
    {boardQuadrant[2, 2] = 3} is sat
    {boardQuadrant[2, 1] = 2} is sat
    {boardQuadrant[1, 1] = 0} is sat
}


test suite for wellformed {
    example fullBoard1 is {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 4 +
                            0 -> 1 -> 3 +
                            0 -> 2 -> 1 +
                            0 -> 3 -> 2 +
                            1 -> 0 -> 1 +
                            1 -> 1 -> 2 +
                            1 -> 2 -> 4 +
                            1 -> 3 -> 3 +
                            2 -> 0 -> 2 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 3 +
                            2 -> 3 -> 4 +
                            3 -> 0 -> 3 +
                            3 -> 1 -> 4 +
                            3 -> 2 -> 2 +
                            3 -> 3 -> 1)
    }

    example halfEmpty is {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 2 -> 3 +
                            0 -> 3 -> 2 +
                            1 -> 2 -> 1 +
                            1 -> 3 -> 4 +
                            2 -> 0 -> 4 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 2 +
                            3 -> 0 -> 2 +
                            3 -> 1 -> 3)
    }

    example allSameEntry2 is not {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 1 -> 1 +
                            0 -> 2 -> 1 +
                            0 -> 3 -> 1 +
                            1 -> 0 -> 1 +
                            1 -> 1 -> 1 +
                            1 -> 2 -> 1 +
                            1 -> 3 -> 1 +
                            2 -> 0 -> 1 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 1 +
                            2 -> 3 -> 1 +
                            3 -> 0 -> 1 +
                            3 -> 1 -> 1 +
                            3 -> 2 -> 1 +
                            3 -> 3 -> 1)
    }

    example oneViolation2 is not {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 1 -> 1 +
                            0 -> 2 -> 4 +
                            0 -> 3 -> 3 +
                            1 -> 0 -> 4 +
                            1 -> 1 -> 3 +
                            1 -> 2 -> 2 +
                            1 -> 3 -> 1 +
                            2 -> 0 -> 3 + 
                            2 -> 1 -> 4 + 
                            2 -> 2 -> 1 +
                            2 -> 3 -> 2 +
                            3 -> 0 -> 2 +
                            3 -> 1 -> 1 +
                            3 -> 2 -> 4 +
                            3 -> 3 -> 3)
    }

    example emptyBoard is {some b: Board | wellformed[b]} for {
        Board = `Board0
    }

    example valMoreThan4 is not {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 5)
    }

    example valLesserThan1 is not {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 0)
    }

    example rowIndexMoreThan3 is not {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 4 -> 2)
    }

    example colIndexMoreThan3 is not {some b: Board | wellformed[b]} for {
        Board = `Board0
        board = `Board0 -> (4 -> 0 -> 2)
    }
}

test suite for win {
    example fullBoard is {some b: Board | win[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 4 +
                            0 -> 1 -> 3 +
                            0 -> 2 -> 1 +
                            0 -> 3 -> 2 +
                            1 -> 0 -> 1 +
                            1 -> 1 -> 2 +
                            1 -> 2 -> 4 +
                            1 -> 3 -> 3 +
                            2 -> 0 -> 2 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 3 +
                            2 -> 3 -> 4 +
                            3 -> 0 -> 3 +
                            3 -> 1 -> 4 +
                            3 -> 2 -> 2 +
                            3 -> 3 -> 1)
    }

    example fullBoard2 is {some b: Board | win[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 1 -> 2 +
                            0 -> 2 -> 4 +
                            0 -> 3 -> 3 +
                            1 -> 0 -> 4 +
                            1 -> 1 -> 3 +
                            1 -> 2 -> 2 +
                            1 -> 3 -> 1 +
                            2 -> 0 -> 3 + 
                            2 -> 1 -> 4 + 
                            2 -> 2 -> 1 +
                            2 -> 3 -> 2 +
                            3 -> 0 -> 2 +
                            3 -> 1 -> 1 +
                            3 -> 2 -> 4 +
                            3 -> 3 -> 3)
    }

    example allSameEntry is {some b: Board | win[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 1 -> 1 +
                            0 -> 2 -> 1 +
                            0 -> 3 -> 1 +
                            1 -> 0 -> 1 +
                            1 -> 1 -> 1 +
                            1 -> 2 -> 1 +
                            1 -> 3 -> 1 +
                            2 -> 0 -> 1 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 1 +
                            2 -> 3 -> 1 +
                            3 -> 0 -> 1 +
                            3 -> 1 -> 1 +
                            3 -> 2 -> 1 +
                            3 -> 3 -> 1)
    }

    example oneViolation is {some b: Board | win[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 1 -> 1 +
                            0 -> 2 -> 4 +
                            0 -> 3 -> 3 +
                            1 -> 0 -> 4 +
                            1 -> 1 -> 3 +
                            1 -> 2 -> 2 +
                            1 -> 3 -> 1 +
                            2 -> 0 -> 3 + 
                            2 -> 1 -> 4 + 
                            2 -> 2 -> 1 +
                            2 -> 3 -> 2 +
                            3 -> 0 -> 2 +
                            3 -> 1 -> 1 +
                            3 -> 2 -> 4 +
                            3 -> 3 -> 3)
    }

    example oneCellEmpty is not {some b: Board | win[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 2 -> 4 +
                            0 -> 3 -> 3 +
                            1 -> 0 -> 4 +
                            1 -> 1 -> 3 +
                            1 -> 2 -> 2 +
                            1 -> 3 -> 1 +
                            2 -> 0 -> 3 + 
                            2 -> 1 -> 4 + 
                            2 -> 2 -> 1 +
                            2 -> 3 -> 2 +
                            3 -> 0 -> 2 +
                            3 -> 1 -> 1 +
                            3 -> 2 -> 4 +
                            3 -> 3 -> 3)
    }

    example halfEmpty2 is not {some b: Board | win[b]} for {
        Board = `Board0
        board = `Board0 -> (0 -> 0 -> 1 +
                            0 -> 2 -> 3 +
                            0 -> 3 -> 2 +
                            1 -> 2 -> 1 +
                            1 -> 3 -> 4 +
                            2 -> 0 -> 4 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 2 +
                            3 -> 0 -> 2 +
                            3 -> 1 -> 3)
    }

    example emptyBoard2 is not {some b: Board | win[b]} for {
        Board = `Board0
    }
}

test suite for move {
    // can manually input the values for row col val 
    example oneEmpty is {some pre, post: Board | move[pre, post, 3, 3, 1]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 0 -> 4 +
                            0 -> 1 -> 3 +
                            0 -> 2 -> 1 +
                            0 -> 3 -> 2 +
                            1 -> 0 -> 1 +
                            1 -> 1 -> 2 +
                            1 -> 2 -> 4 +
                            1 -> 3 -> 3 +
                            2 -> 0 -> 2 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 3 +
                            2 -> 3 -> 4 +
                            3 -> 0 -> 3 +
                            3 -> 1 -> 4 +
                            3 -> 2 -> 2) +
                    `Board1 -> (0 -> 0 -> 4 +
                            0 -> 1 -> 3 +
                            0 -> 2 -> 1 +
                            0 -> 3 -> 2 +
                            1 -> 0 -> 1 +
                            1 -> 1 -> 2 +
                            1 -> 2 -> 4 +
                            1 -> 3 -> 3 +
                            2 -> 0 -> 2 + 
                            2 -> 1 -> 1 + 
                            2 -> 2 -> 3 +
                            2 -> 3 -> 4 +
                            3 -> 0 -> 3 +
                            3 -> 1 -> 4 +
                            3 -> 2 -> 2 +
                            3 -> 3 -> 1)
    }
    example halfEmpty3 is {some pre, post: Board | move[pre, post, 2, 3, 3]} for {
    Board = `Board0 + `Board1
    board = `Board0 -> (0 -> 0 -> 1 +
                        0 -> 2 -> 3 +
                        0 -> 3 -> 2 +
                        1 -> 2 -> 1 +
                        1 -> 3 -> 4 +
                        2 -> 0 -> 4 + 
                        2 -> 1 -> 1 + 
                        2 -> 2 -> 2 +
                        3 -> 0 -> 2 +
                        3 -> 1 -> 3) +
            `Board1 -> (0 -> 0 -> 1 +
                        0 -> 2 -> 3 +
                        0 -> 3 -> 2 +
                        1 -> 2 -> 1 +
                        1 -> 3 -> 4 +
                        2 -> 0 -> 4 + 
                        2 -> 1 -> 1 + 
                        2 -> 2 -> 2 +
                        2 -> 3 -> 3 +
                        3 -> 0 -> 2 +
                        3 -> 1 -> 3)
    }
    

    
    example EmptyExceptOne is {some pre, post: Board | move[pre, post, 0, 0, 1]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 1 -> 2) +
                `Board1 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 1)
    }

    example wrongRowInput is not {some pre, post: Board | move[pre, post, 1, 0, 1]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 1 -> 2) +
                `Board1 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 1)
    }

    example wrongColInput is not {some pre, post: Board | move[pre, post, 0, 1, 1]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 1 -> 2) +
                `Board1 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 1)
    }

    example wrongValInput is not {some pre, post: Board | move[pre, post, 0, 0, 2]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 1 -> 2) +
                `Board1 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 1)
    }

    example valLargerThan4 is not {some pre, post: Board | move[pre, post, 0, 0, 5]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 1 -> 2) +
                `Board1 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 5)
    }

    example valLessThan1 is not {some pre, post: Board | move[pre, post, 0, 0, 0]} for {
        Board = `Board0 + `Board1
        board = `Board0 -> (0 -> 1 -> 2) +
                `Board1 -> (0 -> 1 -> 2 +
                            0 -> 0 -> 0)
    }
}