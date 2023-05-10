#lang forge/bsl

open "temp_4x4.frg"

test suite for InitState {
    // example of an initial state (all hands have 1 finger up)
    example initState is { some s: State | InitState[s] } for {
        State = `S0 -- a trace with one state for simplicity
        A = `A0
        B = `B0
        Person = A + B
        turn = `S0 -> `A0

        Hand = `Hand0 + `Hand1 + `Hand2 + `Hand3
        fingers = `Hand0 -> 5 + `Hand1 -> 5 + `Hand2 -> 5 + `Hand3 -> 5
        up = `Hand0 -> 1 + `Hand1 -> 1 + `Hand2 -> 1 + `Hand3 -> 1

        HandSpread = `Handspread0 + `Handspread1
        left = `Handspread0 -> `Hand0 + `Handspread1 -> `Hand2
        right = `Handspread0 -> `Hand1 + `Handspread1 -> `Hand3

        spread = `S0 -> `A0 -> `Handspread0 + `S0 -> `B0 -> `Handspread1
    }
}