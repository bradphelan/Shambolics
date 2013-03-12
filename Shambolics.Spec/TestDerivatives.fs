namespace Shambolics.Spec

open FsUnit
open NUnit.Framework
open Microsoft.FSharp.Quotations
open Shambolics.Calculus
open Shambolics.Print
open FSharpx.Linq.QuotationEvaluation
open System
open Microsoft.FSharp.Linq.RuntimeHelpers

type EqualsAsString (e:obj)= 
    inherit NUnit.Framework.Constraints.Constraint()
    
    let expected = e
    
    override x.Matches(actual:obj)=
        x.actual <- actual
        x.actual.ToString() = expected.ToString()
        
    override x.WriteDescriptionTo(writer)=
        writer.WriteExpectedValue(expected)
        
    override x.WriteActualValueTo(writer)=
        writer.WriteActualValue(x.actual)
   
[<TestFixture>]
type ``This is a test for symbolic derivatives`` ()=

    let equalExpr (x:Expr<'t>) = new EqualsAsString(x)
    
    [<Test>] 
    member x.``Derivative should work`` ()=
    
        let e = <@ (fun (y:double) -> y * y) @>
        let d = der e
        
        let l:double->double=LeafExpressionConverter.EvaluateQuotation d :?> ( double -> double )
        d |> should equalExpr <@ fun (y:double) -> 2.0 * y @>
             
        
    [<Test>] 
    member x.``Sin should differentiate`` ()=
        
        let e = <@ fun (y:double) -> Math.Sin( 2.0 * y * y ) @>
        let d = der e
        
        d |> should equalExpr <@ fun (y:double) -> 4.0 * y * Math.Cos(2.0 * y * y ) @>
        
    [<Test>] 
    member x.``Cos should differentiate`` ()=
        
        let e = <@ fun (y:double) -> Math.Cos( 2.0 * y * y ) @>
        let d = der e
        
        d |> should equalExpr <@ fun (y:double) -> - (4.0 * y) * Math.Sin(2.0 * y * y ) @>
        
    [<Test>] 
    member x.``Quotient Rule`` ()=
        
        let e = <@ fun (y:double) -> 1.0 / y @>
        let d = der e
        
        d |> should equalExpr <@ fun (y:double) ->  -1.0 / Math.Pow(y,2.0) @>

    [<Test>] 
    member x.``Multipy by zero should work`` ()=
    
        let e = simplify <@ fun x -> 0.0 * x @>
        e |> should equalExpr <@ fun x-> 0.0 @>
        
    [<Test>] 
    member x.``Add zero should work`` ()=
        
        let e = simplify <@ fun x -> 0.0 + x @>
        e |> should equalExpr <@ fun x-> x @>
        
        
    [<Test>] 
    member x.``Simplify addition of similar terms should work`` ()=
        let e = simplify <@ fun (x:double) -> (x+2.0) + (x+2.0) @>
        e |> should equalExpr <@ fun x-> 2.0 * (x + 2.0) @>

    [<Test>] 
    member x.``Extract common factors`` ()=
        let e = simplify <@ fun (x:double) -> (x * 2.0) + (x * 3.0) @>
        e |> should equalExpr <@ fun x-> x * 5.0  @> 
        
    [<Test>] 
    member x.``Extract common factors duplicated`` ()=
        let e = simplify <@ fun (x:double) -> (x * 1.0 ) + (1.0 * x ) @>
        e |> should equalExpr <@ fun x-> x * 2.0  @> 
        
    [<Test>] 
    member x.``Extract common factors duplicated again`` ()=
        let e = simplify <@ fun (x:double) -> (1.0 * x ) + (x * 1.0) @>
        e |> should equalExpr <@ fun x-> 2.0 * x  @> 
