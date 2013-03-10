namespace Shambolics

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns


module Print =
    let println expr =
        let rec print expr =
            match expr with
            | Application(expr1, expr2) ->
                // Function application.
                print expr1
                printf " "
                print expr2
            | SpecificCall <@@ (+) @@> (_, _, exprList) ->
                printf "("
                print exprList.Head
                printf " + "
                print exprList.Tail.Head
                printf ")"
            | SpecificCall <@@ (*) @@> (_, _, exprList) ->
                print exprList.Head
                printf " * "
                print exprList.Tail.Head
            | SpecificCall <@@ (/) @@> (_, _, exprList) ->
                print exprList.Head
                printf " / "
                print exprList.Tail.Head
            | Call(exprOpt, methodInfo, exprList) ->
                // Method or module function call. 
                match exprOpt with
                | Some expr -> print expr
                | None -> printf "%s" methodInfo.DeclaringType.Name
                printf ".%s(" methodInfo.Name
                if (exprList.IsEmpty) then printf ")" else
                print exprList.Head
                for expr in exprList.Tail do
                    printf ","
                    print expr
                printf ")"
            | Int32(n) ->
                printf "%d" n
            | Lambda(param, body) ->
                // Lambda expression.
                printf "fun (%s:%s) -> " param.Name (param.Type.ToString())
                print body
            | Let(var, expr1, expr2) ->
                // Let binding. 
                if (var.IsMutable) then
                    printf "let mutable %s = " var.Name
                else
                    printf "let %s = " var.Name
                print expr1
                printf " in "
                print expr2
            | PropertyGet(_, propOrValInfo, _) ->
                printf "%s" propOrValInfo.Name
            | String(str) ->
                printf "%s" str
            | Value(value, typ) ->
                printf "%s" (value.ToString())
            | Var(var) ->
                printf "%s" var.Name
            | _ -> printf "%s" (expr.ToString())
        print expr
        printfn "" 
