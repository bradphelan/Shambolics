namespace Shambolics

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open System
open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Quotations

open FSharpx.Linq.QuotationEvaluation
open Microsoft.FSharp.Linq.RuntimeHelpers

module Calculus =

    let rec simplify quotation =
    
        match quotation with
        
        | SpecificCall <@ (+) @> (_,types,l::r::[]) -> 
        
            let ll = simplify l
            let rr = simplify r
            
            
            match (ll,rr) with
            | (Double 0.0, Double 0.0) -> <@@ 0.0 @@>
            | (Double 0.0, v) -> v
            | (v, Double 0.0) -> v
            | (Double a, Double b) -> 
                Expr.Value (a + b)
            | _ -> <@@ (%%ll:double) + (%%rr:double) @@>
                
                
        | SpecificCall <@ (/) @> (_,types,l::r::[]) -> 
        
            let ll = simplify l
            let rr = simplify r
            
            match (ll,rr) with
            | (_, Double 0.0) -> failwith "divide by zero"
            | (Double 0.0, _) -> <@@ 0.0 @@>
            | (Double a, Double b) -> 
                Expr.Value (a / b)
            | (v, Double 1.0) -> v 
            | _ -> <@@ (%%ll:double) / (%%rr:double) @@>
            
                
        | SpecificCall <@ (*) @> (_,types,l::r::[]) -> 
        
            let ll = simplify l
            let rr = simplify r
            
            match (ll,rr) with
            | (_, Double 0.0) -> <@@ 0.0 @@>
            | (Double 0.0, _) -> <@@ 0.0 @@>
            | (Double 1.0, v) -> v 
            | (v, Double 1.0) -> v 
            | (Double a, Double b) -> 
                Expr.Value (a * b)
            | _ -> <@@ (%%ll:double) * (%%rr:double) @@>
            
            
        | ExprShape.ShapeVar v ->
            Expr.Var v
            
        | ExprShape.ShapeLambda (v,expr) -> Expr.Lambda (v, simplify expr)
        
        | ExprShape.ShapeCombination (o, exprs) -> ExprShape.RebuildShapeCombination (o,List.map simplify exprs)
    
    let rec der_impl param quotation =
   
        let (|X|_|) input = if input = param then Some(X) else None
         
        match quotation with
        
        | SpecificCall <@ (*) @> (_,types,l::r::[]) -> 
            let dl = der_impl param l
            let dr = der_impl param r
            <@@ (%%dl:double) * (%%r:double) + (%%l:double) * (%%dr:double) @@>
            
        | SpecificCall <@ Math.Sin @> (_,_types, arg::_) ->
            let di = der_impl param arg
            <@@ (%%di:double) * Math.Cos( (%%arg:double) ) @@> 
            
         | Double _ ->
            <@@ 0.0 @@>
            
        | ExprShape.ShapeVar v -> 
            match v with 
            | X -> <@@ 1.0 @@>
            | _ -> (Expr.Var v)
            
        | ExprShape.ShapeLambda (v,expr) -> Expr.Lambda (v,der_impl param expr)
        
        | ExprShape.ShapeCombination (o, exprs) -> ExprShape.RebuildShapeCombination (o,List.map (fun e -> der_impl param e ) exprs)
        
    let rec der expr =
        match expr with
        | Lambda(param, body) ->
            Expr.Lambda(param, (der_impl param body))
            |> simplify
        | _ -> failwith "oops"
