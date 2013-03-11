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
    
        let (|Same|_|) x =
            match x with
            | (r,l) when r = l -> Some(Same(l))
            | _ -> None
            
        let (|Multiply|_|) x =
            match x with    
            | SpecificCall <@ (*) @> (_,_,l::r::[]) -> Some(Multiply(l,r))
            | _ -> None 
            
        let (|Add|_|) x =
            match x with    
            | SpecificCall <@ (+) @> (_,_,l::r::[]) -> Some(Add(l,r))
            | _ -> None 
            
        let (|Divide|_|) x =
            match x with    
            | SpecificCall <@ (+) @> (_,_,l::r::[]) -> Some(Divide(l,r))
            | _ -> None 
            
        let (|ConstantMultiply|_|) x =
            match x with
            | Multiply( Double v, r) -> Some(ConstantMultiply(v,r))
            | Multiply( l, Double v) -> Some(ConstantMultiply(v,l))    
            | _ -> None
            
        let (|MultiplyAdd|_|) x =
            match x with    
            | Add ( Multiply (ll,lr), Multiply(rl, rr)) -> Some( MultiplyAdd( (ll,lr,rl,rr)))
            | _ -> None    
            
        let Multiply3(a,b,c) = 
            let e = simplify <@@(%%b:double) + (%%c:double) @@>
            simplify <@@ (%%a: double) * (%%e:double) @@>
        
        let (|CommonFactor|_|) x =
            match x with
            | MultiplyAdd(al,ar,bl,br) when al = bl ->
                Some(CommonFactor(Multiply3(al,ar,br)))
                
            | MultiplyAdd (al,ar,bl,br) when al = br ->
                Some(CommonFactor(Multiply3(al,ar,bl)))
                
            | MultiplyAdd(al,ar,bl,br) when ar = bl ->
                Some(CommonFactor(Multiply3(ar,al,br)))
                
            | MultiplyAdd(al,ar,bl,br) when ar = br ->
                Some(CommonFactor(Multiply3(ar,al,bl)))
                
            | _ -> None
    
        
        Console.WriteLine(quotation)
        
        match quotation with
        
        | CommonFactor e -> e
        
        | Add (l,r) ->
        
            let ll = simplify l
            let rr = simplify r
            
            match (ll,rr) with
            | (Double 0.0, Double 0.0) -> Expr.Value 0.0
            | (Double 0.0, v) -> v
            | (v, Double 0.0) -> v
            | (Double a, Double b) -> Expr.Value (a + b)
            | Same l -> <@@ 2.0 * (%%l:double) @@>
            | _ -> <@@ (%%ll:double) + (%%rr:double) @@>
                
                
        | Divide (l,r) ->
        
            let ll = simplify l
            let rr = simplify r
            
            match (ll,rr) with
            | (_, Double 0.0)      -> failwith "divide by zero"
            | (Double 0.0, _)      -> Expr.Value 0.0
            | (Double a, Double b) -> Expr.Value (a / b)
            | (v, Double 1.0)      -> v
            | _                    -> <@@ (%%ll:double) / (%%rr:double) @@>
            
        | ConstantMultiply( c0, ConstantMultiply(c1, v)) ->    
            let c = Expr.Value ( c0 * c1 )
            simplify <@@ (%%c:double) * (%%v:double) @@>    
            
        | ConstantMultiply( 0.0, v)      -> Expr.Value 0.0
        | ConstantMultiply( 1.0, v)      -> v
        | ConstantMultiply( c, Double v) -> Expr.Value (c * v )
        | Multiply (a,b)                 -> 
            let sa = simplify a
            let sb = simplify b
            Console.WriteLine("--")
            Console.WriteLine(sa)
            Console.WriteLine(sb)
            let e = <@@ (%%sa:double) * (%%sb:double) @@>
            if sa = a && sb = b then
                e
            else
                simplify e
            
            
        | ExprShape.ShapeVar v                  -> Expr.Var v
        | ExprShape.ShapeLambda (v,expr)        -> Expr.Lambda (v, simplify expr)
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

        | SpecificCall <@ Math.Cos @> (_,_types, arg::_) ->
            let di = der_impl param arg
            <@@ - (%%di:double) * Math.Sin( (%%arg:double) ) @@> 
            
         | Double _ -> Expr.Value 0.0
            
        | ExprShape.ShapeVar v -> 
            match v with 
            | X -> Expr.Value 1.0
            | _ -> Expr.Var v
            
        | ExprShape.ShapeLambda (v,expr) -> Expr.Lambda (v,der_impl param expr)
        
        | ExprShape.ShapeCombination (o, exprs) -> ExprShape.RebuildShapeCombination (o,List.map (fun e -> der_impl param e ) exprs)
        
    let rec der expr =
        match expr with
        | Lambda(param, body) ->
            Expr.Lambda(param, (der_impl param body) |> simplify)
        | _ -> failwith "oops"
