// Learn more about F# at http://docs.microsoft.com/dotnet/fsharp

open System
open FsCheck

//
// The clock
//

type ClockState =
    {
    Hours: int
    Minutes: int
    Seconds: int
    }

let Tick (clock: ClockState) =
    match clock with
    | {Hours = 23; Minutes = 59; Seconds = 59} -> {Hours = 0; Minutes = 0; Seconds = 0}
    | {Hours = h; Minutes = 59; Seconds = 59} -> {Hours = h + 1; Minutes = 0; Seconds = 0}
    | {Hours = _; Minutes = m; Seconds = 59} -> {clock with Minutes = m + 1; Seconds = 0}
    | {Hours = _; Minutes = _; Seconds = s} -> {clock with Seconds = s + 1}

//
// Testing the clock
//

// Generate valid initial clock states.
// There's no point having a Tick function that tries to recover from a nonsensical time, e.g. negative numbers.
type Generators =
    static member ClockStateGenerator() =
        {
        new Arbitrary<ClockState>() with
            override x.Generator = Gen.zip3 (Gen.choose(0, 23)) (Gen.choose(0, 59)) (Gen.choose(0, 59)) |> Gen.map (fun (h, m, s) -> {Hours = h; Minutes = m; Seconds = s})
            override x.Shrinker t = Seq.empty
        }

// Analogous to the following TLA+ 
// (* INVARIANTS *)
// TypeOK == /\ h \in 0..23
//           /\ m \in 0..60
//           /\ s \in 0..59
type ClockInvariants = 
    static member ``Hours in range`` (clock:ClockState) = clock.Hours >= 0 && clock.Hours <= 23
    static member ``Minutes in range`` (clock:ClockState) = clock.Minutes >= 0 && clock.Hours <= 59
    static member ``Seconds in range`` (clock:ClockState) = clock.Seconds >= 0 && clock.Hours <= 59
    static member ``Hours in range preserved`` (clock:ClockState) = ClockInvariants.``Hours in range`` (Tick clock)
    static member ``Minutes in range preserved`` (clock:ClockState) = ClockInvariants.``Minutes in range`` (Tick clock)
    static member ``Seconds in range preserved`` (clock:ClockState) = ClockInvariants.``Seconds in range`` (Tick clock)

// Possibility: Use an Hours-Minutes clock for model-based testing of an Hours-Minutes-Seconds clock.
[<EntryPoint>]
let main argv =
    Arb.register<Generators>() |> ignore
    Check.VerboseAll<ClockInvariants>()
    0