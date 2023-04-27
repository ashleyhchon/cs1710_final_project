#lang forge/bsl

sig Board {
    board: pfunc Int -> Int -> Int
}

-- helper function for assigning which quadrant of the board the entry is in
-- top-left = 0, top-right = 1, bottom-left = 2, bottom-right = 3
fun boardQuadrant(row: Int, col: Int): Int {
    (row > 1 and col > 1) => 3 else
    (row > 1 and col <= 1) => 2 else
    (row <= 1 and col > 1) => 1 else 0
}

pred wellformed[b: Board] {
    -- no board beyond row and column indices of 0-3
    all row, col: Int | {
        (row < 0 or row > 3 or col < 0 or col > 3) implies
        no b.board[row][col]
    }

    -- all entries are between 1-4
    all row, col: Int | {
        (row >= 0 and row <= 3 and col >= 0 and col <= 3) implies
        some b.board[row][col] =>
        (b.board[row][col] > 0 and b.board[row][col] < 5)
    }

    -- if the entry values are the same, they can't be in the same row, column, or quadrant
    all r1, c1, r2, c2: Int | {
        (not (r1 = r2 and c1 = c2) and some b.board[r1][c1] and some b.board[r2][c2]) => {
            (b.board[r1][c1] = b.board[r2][c2]) <=>  --  entry values are the same
            ((r1 != r2 and c1 != c2 and boardQuadrant[r1, c1] != boardQuadrant[r2, c2]) and (b.board[r1][c1] = b.board[r2][c2]))
        }
    }
}

// run {
//     some b: Board | wellformed[b]
// } for exactly 1 Board

-- all entries in the board are filled
pred win[b: Board] {
    all row, col: Int | (row >= 0 and row <= 3 and col >= 0 and col <= 3) => {
        some b.board[row][col]
    } 
}

pred starting[b: Board] {
    // edit to randomly fill in initial sudoku board

    // would basically be like solving, but opposite
    // start from a board that is win[b] and wellformed[b]
    // remove one cell
    // continue while there is only one unique solution
    // how to find that it can only have one unique solution? 
    // - reachable? but not sure how to quantify

    b.board[0][0] = 4
    b.board[0][1] = 3
    b.board[0][2] = 1
    b.board[0][3] = 2

    no b.board[1][0] // = 1
    b.board[1][1] = 2
    b.board[1][2] = 4
    b.board[1][3] = 3

    b.board[2][0] = 2
    b.board[2][1] = 1
    b.board[2][2] = 3
    no b.board[2][3] // = 4

    b.board[3][0] = 3
    b.board[3][1] = 4
    b.board[3][2] = 2
    b.board[3][3] = 1
}

// run {
//     some b: Board | win[b] and lastStep[b]
// } for exactly 1 Board

pred move[pre: Board, post: Board, row: Int, col: Int, val: Int] {
    -- GUARD (what needs to hold about the pre-state?)
    pre != post
    no pre.board[row][col] -- no move already there
    row <= 3
    row >= 0 
    col <= 3
    col >= 0
    -- No win yet (guard)
    not win[pre]
    
    -- ACTION (what does the post-state then look like?)
    val <= 4
    val >= 1
    post.board[row][col] = val -- set the value in the post board

    -- makes sure nothing else changes in the board
    all row2: Int, col2: Int | (row != row2 or col != col2) implies {                
        post.board[row2][col2] = pre.board[row2][col2]
    }  

}

one sig Game {
  initialState: one Board,
  next: pfunc Board -> Board
}

pred traces {
    starting[Game.initialState]
    all b: Board | some Game.next[b] implies {
        some row, col, val: Int | {
            move[b, Game.next[b], row, col, val]            
        }
    } else win[b]
}

run {
    all b: Board | wellformed[b]
    traces
} for 3 Board, 4 Int for {next is linear}

// run {
//     all b: Board | win[b] and wellformed[b]
// }
