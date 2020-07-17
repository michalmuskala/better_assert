-module(ba_map_call_transform).

%% A transformer to alter a specific "marker" call.

-export([transform/3]).

transform(Forms, MFA, Fun) ->
    [form(Form, MFA, Fun) || Form <- Forms].

form({function,Line,Name,Arity,Clauses}, MFA, Fun) ->
    {function,Line,Name,Arity,clauses(Clauses, MFA, Fun)};
form(Other, _MFA, _Fun) -> Other.

clauses(Clauses, MFA, Fun) -> [clause(Clause, MFA, Fun) || Clause <- Clauses].

clause({clause,Line,Head,Guards,Body}, MFA, Fun) ->
    {clause,Line,Head,Guards,exprs(Body, MFA, Fun)}.

exprs(Exprs, MFA, Fun) -> [expr(Expr, MFA, Fun) || Expr <- Exprs].

expr({cons,Line,H0,T0}, MFA, Fun) ->
    H1 = expr(H0, MFA, Fun),
    T1 = expr(T0, MFA, Fun),
    {cons,Line,H1,T1};
expr({lc,Line,E0,Qs0}, MFA, Fun) ->
    Qs1 = lc_bc_quals(Qs0, MFA, Fun),
    E1 = expr(E0, MFA, Fun),
    {lc,Line,E1,Qs1};
expr({bc,Line,E0,Qs0}, MFA, Fun) ->
    Qs1 = lc_bc_quals(Qs0, MFA, Fun),
    E1 = expr(E0, MFA, Fun),
    {bc,Line,E1,Qs1};
expr({tuple,Line,Es0}, MFA, Fun) ->
    Es1 = exprs(Es0, MFA, Fun),
    {tuple,Line,Es1};
expr({map,Line,Map0,Es0}, MFA, Fun) ->
    [Map1|Es1] = exprs([Map0|Es0], MFA, Fun),
    {map,Line,Map1,Es1};
expr({map,Line,Es0}, MFA, Fun) ->
    Es1 = exprs(Es0, MFA, Fun),
    {map,Line,Es1};
expr({map_field_assoc,Line,K,V}, MFA, Fun) ->
    Ke = expr(K, MFA, Fun),
    Ve = expr(V, MFA, Fun),
    {map_field_assoc,Line,Ke,Ve};
expr({map_field_exact,Line,K,V}, MFA, Fun) ->
    Ke = expr(K, MFA, Fun),
    Ve = expr(V, MFA, Fun),
    {map_field_exact,Line,Ke,Ve};
expr({record_index,Line,Name,Field0}, MFA, Fun) ->
    Field1 = expr(Field0, MFA, Fun),
    {record_index,Line,Name,Field1};
expr({record,Line,Name,Inits0}, MFA, Fun) ->
    Inits1 = record_inits(Inits0, MFA, Fun),
    {record,Line,Name,Inits1};
expr({record_field,Line,Rec0,Name,Field0}, MFA, Fun) ->
    Rec1 = expr(Rec0, MFA, Fun),
    Field1 = expr(Field0, MFA, Fun),
    {record_field,Line,Rec1,Name,Field1};
expr({record,Line,Rec0,Name,Upds0}, MFA, Fun) ->
    Rec1 = expr(Rec0, MFA, Fun),
    Upds1 = record_updates(Upds0, MFA, Fun),
    {record,Line,Rec1,Name,Upds1};
expr({record_field,Line,Rec0,Field0}, MFA, Fun) ->
    Rec1 = expr(Rec0, MFA, Fun),
    Field1 = expr(Field0, MFA, Fun),
    {record_field,Line,Rec1,Field1};
expr({block,Line,Es0}, MFA, Fun) ->
    Es1 = exprs(Es0, MFA, Fun),
    {block,Line,Es1};
expr({'if',Line,Cs0}, MFA, Fun) ->
    Cs1 = clauses(Cs0, MFA, Fun),
    {'if',Line,Cs1};
expr({'case',Line,E0,Cs0}, MFA, Fun) ->
    E1 = expr(E0, MFA, Fun),
    Cs1 = clauses(Cs0, MFA, Fun),
    {'case',Line,E1,Cs1};
expr({'receive',Line,Cs0}, MFA, Fun) ->
    Cs1 = clauses(Cs0, MFA, Fun),
    {'receive',Line,Cs1};
expr({'receive',Line,Cs0,To0,ToEs0}, MFA, Fun) ->
    To1 = expr(To0, MFA, Fun),
    ToEs1 = exprs(ToEs0, MFA, Fun),
    Cs1 = clauses(Cs0, MFA, Fun),
    {'receive',Line,Cs1,To1,ToEs1};
expr({'try',Line,Es0,Scs0,Ccs0,As0}, MFA, Fun) ->
    Es1 = exprs(Es0, MFA, Fun),
    Scs1 = clauses(Scs0, MFA, Fun),
    Ccs1 = clauses(Ccs0, MFA, Fun),
    As1 = exprs(As0, MFA, Fun),
    {'try',Line,Es1,Scs1,Ccs1,As1};
expr({'fun',Line,Body}, MFA, Fun) ->
    case Body of
        {clauses,Cs0} ->
            Cs1 = clauses(Cs0, MFA, Fun),
            {'fun',Line,{clauses,Cs1}};
        {function,F,A} ->
            {'fun',Line,{function,F,A}};
        {function,M0,F0,A0} ->
            M = expr(M0, MFA, Fun),
            F = expr(F0, MFA, Fun),
            A = expr(A0, MFA, Fun),
            {'fun',Line,{function,M,F,A}}
    end;
expr({named_fun,Loc,Name,Cs}, MFA, Fun) ->
    {named_fun,Loc,Name,clauses(Cs, MFA, Fun)};
expr({call,Line,{remote,_,{atom,_,M},{atom,_,F}}=R,As0} = Call, MFA, Fun) ->
    case {M, F, length(As0)} of
        MFA -> 
            Fun(Call);
        _ -> 
            As1 = exprs(As0, MFA, Fun),
            {call, Line, R, As1}
    end;
expr({call,Line,F0,As0}, MFA, Fun) ->
    F1 = expr(F0, MFA, Fun),
    As1 = exprs(As0, MFA, Fun),
    {call,Line,F1,As1};
expr({'catch',Line,E0}, MFA, Fun) ->
    E1 = expr(E0, MFA, Fun),
    {'catch',Line,E1};
expr({match,Line,P,E0}, MFA, Fun) ->
    E1 = expr(E0, MFA, Fun),
    {match,Line,P,E1};
expr({op,Line,Op,A0}, MFA, Fun) ->
    A1 = expr(A0, MFA, Fun),
    {op,Line,Op,A1};
expr({op,Line,Op,L0,R0}, MFA, Fun) ->
    L1 = expr(L0, MFA, Fun),
    R1 = expr(R0, MFA, Fun),
    {op,Line,Op,L1,R1};
expr({remote,Line,M0,F0}, MFA, Fun) ->
    M1 = expr(M0, MFA, Fun),
    F1 = expr(F0, MFA, Fun),
    {remote,Line,M1,F1};
expr(Other, _MFA, _Fun) -> Other.

record_inits([{record_field,Lf,{atom,La,F},Val0}|Is], MFA, Fun) ->
    Val1 = expr(Val0, MFA, Fun),
    [{record_field,Lf,{atom,La,F},Val1}|record_inits(Is, MFA, Fun)];
record_inits([{record_field,Lf,{var,La,'_'},Val0}|Is], MFA, Fun) ->
    Val1 = expr(Val0, MFA, Fun),
    [{record_field,Lf,{var,La,'_'},Val1}|record_inits(Is, MFA, Fun)];
record_inits([], _MFA, _Fun) -> [].

record_updates([{record_field,Lf,{atom,La,F},Val0}|Us], MFA, Fun) ->
    Val1 = expr(Val0, MFA, Fun),
    [{record_field,Lf,{atom,La,F},Val1}|record_updates(Us, MFA, Fun)];
record_updates([], _MFA, _Fun) -> [].

lc_bc_quals([{generate,Line,P,E0}|Qs], MFA, Fun) ->
    E1 = expr(E0, MFA, Fun),
    [{generate,Line,P,E1}|lc_bc_quals(Qs, MFA, Fun)];
lc_bc_quals([{b_generate,Line,P,E0}|Qs], MFA, Fun) ->
    E1 = expr(E0, MFA, Fun),
    [{b_generate,Line,P,E1}|lc_bc_quals(Qs, MFA, Fun)];
lc_bc_quals([E0|Qs], MFA, Fun) ->
    E1 = expr(E0, MFA, Fun),
    [E1|lc_bc_quals(Qs, MFA, Fun)];
lc_bc_quals([], _MFA, _Fun) -> [].