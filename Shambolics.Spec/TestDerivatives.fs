namespace Shambolics.Spec

open FsUnit
open NUnit.Framework
open Microsoft.FSharp.Quotations
open Shambolics.Calculus
open Shambolics.Print
open FSharpx.Linq.QuotationEvaluation
open System
open Microsoft.FSharp.Linq.RuntimeHelpers

[<TestFixture>]
type ``This is a test for symbolic derivatives`` ()=

    [<Test>] 
    member x.``Derivative should work`` ()=
    
        let e = <@ (fun (y:double) -> y * y) @>
        let d = der e
        
        let l:double->double=LeafExpressionConverter.EvaluateQuotation d :?> ( double -> double )
        
        let x = <@ fun (y:double) -> 1.0 * y + y * 1.0 @>
        d |> should equal x     
             
        
    [<Test>] 
    member x.``Trig should work`` ()=
        
        let e = <@ fun (y:double) -> Math.Sin( 2.0 * y * y ) @>
        let d = der e
        
        println d
        
        d |> should equal <@ fun (y:double) -> 4.0 * y * Math.Cos(2.0 * y * y ) @>
        

    [<Test>] 
    member x.``Multipy by zero should work`` ()=
    
        let e = simplify <@ fun x -> 0.0 * x @>
        e |> should equal <@ fun x-> 0.0 @>
        
    [<Test>] 
    member x.``Add zero should work`` ()=
        
        let e = simplify <@ fun x -> 0.0 + x @>
        e |> should equal <@ fun x-> x @>
