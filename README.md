Shambolics
===========

By: Brad Phelan
Language: F#
License : MIT

Synopsis
========

Cause I wanted to learn FSharp and make something useful. This here is the
beginning of a symbolic calculus engine. It does some basic symbolic derivatives.
For example

    [<Test>] 
    member x.``Trig should work`` ()=
        
        let e = <@ fun (y:double) -> Math.Sin( 2.0 * y * y ) @>
        let d = der e
        
        println d
        
        d |> should equal <@ fun (y:double) -> 4.0 * y * Math.Cos(2.0 * y * y ) @> )

Well it should equal the above but at the moment the simplification engine is
not smart enough so it gets close.

Feel free to hack and add and send pull requests ( with tests )
