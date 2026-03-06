:- module(mi, [
    analyze_predicate/4,          % +Clauses, +Name, +Arity, -Analysis
    extract_recurrence/4,         % +Clauses, +Name, +Arity, -Recurrence
    derive_closed_form/2,         % +Recurrence, -ClosedForm
    verify_on_range/6,            % +Clauses, +Name, +Arity, +ClosedForm, +MaxN, -Report

    parse_file_clauses/2,         % +File, -Clauses
    analyze_file/2,               % +File, -Analyses
    process_file/2,               % +InputFile, +OutputPrefix

    pretty_print_analysis/1,
    write_report_file/2,
    write_rewritten_file/2,

    run_demo/0,
    run_mi_tests/0
]).

:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(library(plunit)).

% =============================================================================
% Public API
% =============================================================================

analyze_predicate(Clauses, Name, Arity, Analysis) :-
    must_be(list, Clauses),
    must_be(atom, Name),
    must_be(integer, Arity),
    Arity >= 2,
    (   extract_recurrence(Clauses, Name, Arity, Recurrence)
    ->  derive_closed_form(Recurrence, ClosedForm),
        Analysis = analysis{
            predicate: Name/Arity,
            status: supported,
            recurrence: Recurrence,
            closed_form: ClosedForm
        }
    ;   detect_accumulator_pattern(Clauses, Name, Arity, Pattern)
    ->  Analysis = analysis{
            predicate: Name/Arity,
            status: supported,
            recurrence: accumulator_only,
            accumulator_pattern: Pattern,
            closed_form: closed_form{
                predicate: Name/Arity,
                kind: normalizable_tail_recursion,
                formula: accumulator_worker(Pattern),
                function: f
            }
        }
    ;   Analysis = analysis{
            predicate: Name/Arity,
            status: unsupported,
            reason: unsupported_recursion_shape
        }
    ).

extract_recurrence(Clauses, Name, Arity, Recurrence) :-
    partition_predicate_clauses(Clauses, Name, Arity, PredClauses),
    PredClauses \= [],
    (   extract_integer_recurrence(PredClauses, Name, Arity, Recurrence)
    ;   extract_list_recurrence(PredClauses, Name, Arity, Recurrence)
    ),
    !.

derive_closed_form(Recurrence, ClosedForm) :-
    get_dict(domain, Recurrence, Domain),
    (   Domain == integer
    ->  (   derive_integer_closed_form(Recurrence, ClosedForm)
        ->  true
        ;   derive_fallback_closed_form(Recurrence, ClosedForm)
        )
    ;   Domain == list
    ->  (   derive_list_closed_form(Recurrence, ClosedForm)
        ->  true
        ;   derive_fallback_closed_form(Recurrence, ClosedForm)
        )
    ;   derive_fallback_closed_form(Recurrence, ClosedForm)
    ).

verify_on_range(Clauses, Name, Arity, ClosedForm, MaxN, Report) :-
    must_be(integer, MaxN),
    MaxN >= 0,
    setup_call_cleanup(
        load_predicate_clauses_temp(Clauses, Refs),
        verify_range_loop(Name, Arity, ClosedForm, 0, MaxN, [], Mismatches),
        unload_temp_clauses(Refs)
    ),
    (   Mismatches == []
    ->  Report = verified(MaxN)
    ;   reverse(Mismatches, Ordered),
        Report = mismatches(Ordered)
    ).

% =============================================================================
% File I/O
% =============================================================================

parse_file_clauses(File, Clauses) :-
    setup_call_cleanup(
        open(File, read, Stream),
        read_terms(Stream, Clauses),
        close(Stream)
    ).

read_terms(Stream, []) :-
    at_end_of_stream(Stream),
    !.
read_terms(Stream, Terms) :-
    read(Stream, Term),
    (   Term == end_of_file
    ->  Terms = []
    ;   Terms = [Term|Rest],
        read_terms(Stream, Rest)
    ).

analyze_file(File, Analyses) :-
    parse_file_clauses(File, Clauses),
    findall(Name/Arity, predicate_indicator_in_clauses(Clauses, Name/Arity), Raw),
    sort(Raw, Preds),
    findall(Analysis,
        ( member(Name/Arity, Preds),
          analyze_predicate(Clauses, Name, Arity, Analysis)
        ),
        Analyses).

process_file(InputFile, OutputPrefix) :-
    analyze_file(InputFile, Analyses),
    atom_concat(OutputPrefix, '.report.txt', ReportFile),
    atom_concat(OutputPrefix, '.rewritten.pl', RewriteFile),
    write_report_file(ReportFile, Analyses),
    write_rewritten_file(RewriteFile, Analyses).

% =============================================================================
% Reporting / rewriting
% =============================================================================

pretty_print_analysis(Analysis) :-
    format("Predicate: ~w~n", [Analysis.predicate]),
    format("Status: ~w~n", [Analysis.status]),
    (   get_dict(recurrence, Analysis, Rec)
    ->  format("Recurrence: ~q~n", [Rec])
    ;   true
    ),
    (   get_dict(closed_form, Analysis, CF)
    ->  format("Closed form: ~q~n", [CF])
    ;   true
    ),
    (   get_dict(reason, Analysis, Reason)
    ->  format("Reason: ~w~n", [Reason])
    ;   true
    ).

write_report_file(File, Analyses) :-
    setup_call_cleanup(
        open(File, write, Stream),
        write_report_stream(Stream, Analyses),
        close(Stream)
    ).

write_report_stream(Stream, Analyses) :-
    format(Stream, "MI Report~n", []),
    format(Stream, "========~n~n", []),
    forall(member(A, Analyses),
           write_analysis_stream(Stream, A)).

write_analysis_stream(Stream, Analysis) :-
    format(Stream, "Predicate: ~w~n", [Analysis.predicate]),
    format(Stream, "Status: ~w~n", [Analysis.status]),
    (   get_dict(recurrence, Analysis, Rec)
    ->  format(Stream, "Recurrence: ~q~n", [Rec])
    ;   true
    ),
    (   get_dict(closed_form, Analysis, CF)
    ->  format(Stream, "Closed form: ~q~n", [CF])
    ;   true
    ),
    (   get_dict(reason, Analysis, Reason)
    ->  format(Stream, "Reason: ~w~n", [Reason])
    ;   true
    ),
    nl(Stream).

write_rewritten_file(File, Analyses) :-
    setup_call_cleanup(
        open(File, write, Stream),
        write_rewritten_stream(Stream, Analyses),
        close(Stream)
    ).

write_rewritten_stream(Stream, Analyses) :-
    format(Stream, "%% Rewritten predicates generated by mi.pl~n~n", []),
    forall(member(A, Analyses),
           write_rewritten_analysis(Stream, A)).

write_rewritten_analysis(Stream, Analysis) :-
    get_dict(status, Analysis, supported),
    get_dict(closed_form, Analysis, ClosedForm),
    write_closed_form_clause(Stream, ClosedForm),
    nl(Stream),
    !.
write_rewritten_analysis(_, _).

write_closed_form_clause(Stream, ClosedForm) :-
    get_dict(predicate, ClosedForm, Pred),
    Pred = Name/2,
    get_dict(kind, ClosedForm, Kind),
    write_closed_form_clause_kind(Stream, Name, Kind, ClosedForm).

write_closed_form_clause_kind(Stream, Name, sum_1_to_n, _ClosedForm) :-
    format(Stream, "~w(N, Value) :-~n", [Name]),
    format(Stream, "    integer(N),~n", []),
    format(Stream, "    N >= 0,~n", []),
    format(Stream, "    Value is (N * (N + 1)) // 2.~n", []).

write_closed_form_clause_kind(Stream, Name, factorial, _ClosedForm) :-
    format(Stream, "~w(N, Value) :-~n", [Name]),
    format(Stream, "    integer(N),~n", []),
    format(Stream, "    N >= 0,~n", []),
    format(Stream, "    mi:factorial_eval(N, Value).~n", []).

write_closed_form_clause_kind(Stream, Name, constant_step_sum, ClosedForm) :-
    get_dict(formula, ClosedForm, (B0 + n * C)),
    format(Stream, "~w(N, Value) :-~n", [Name]),
    format(Stream, "    integer(N),~n", []),
    format(Stream, "    N >= 0,~n", []),
    format(Stream, "    Value is ~w + N * ~w.~n", [B0, C]).

write_closed_form_clause_kind(Stream, Name, constant, ClosedForm) :-
    get_dict(formula, ClosedForm, B0),
    format(Stream, "~w(_N, ~w).~n", [Name, B0]).

write_closed_form_clause_kind(Stream, Name, list_length, _ClosedForm) :-
    format(Stream, "~w(Xs, N) :-~n", [Name]),
    format(Stream, "    is_list(Xs),~n", []),
    format(Stream, "    length(Xs, N).~n", []).

write_closed_form_clause_kind(Stream, Name, list_sum, _ClosedForm) :-
    format(Stream, "~w(Xs, Sum) :-~n", [Name]),
    format(Stream, "    is_list(Xs),~n", []),
    format(Stream, "    sum_list(Xs, Sum).~n", []).

write_closed_form_clause_kind(Stream, Name, normalizable_tail_recursion, ClosedForm) :-
    get_dict(formula, ClosedForm, accumulator_worker(Pattern)),
    format(Stream, "%% Tail-recursive wrapper detected for ~w/2~n", [Name]),
    format(Stream, "%% Pattern: ~q~n", [Pattern]).

write_closed_form_clause_kind(Stream, Name, recurrence_only, ClosedForm) :-
    get_dict(formula, ClosedForm, unsupported_closed_form(Rec)),
    format(Stream, "%% Unsupported closed form for ~w/2: ~q~n", [Name, Rec]).

% =============================================================================
% Clause utilities
% =============================================================================

partition_predicate_clauses(Clauses, Name, Arity, PredClauses) :-
    include(is_target_clause(Name, Arity), Clauses, PredClauses).

is_target_clause(Name, Arity, Clause) :-
    clause_head_body(Clause, Head, _),
    compound(Head),
    functor(Head, Name, Arity).

predicate_indicator_in_clauses(Clauses, Name/Arity) :-
    member(Clause, Clauses),
    \+ is_directive_clause(Clause),
    clause_head_body(Clause, Head, _),
    compound(Head),
    functor(Head, Name, Arity).

is_directive_clause((:- _)).

clause_head_body((Head :- Body), Head, Body) :- !.
clause_head_body(Head, Head, true).

body_to_goals(true, []) :- !.
body_to_goals((A, B), Goals) :- !,
    body_to_goals(A, G1),
    body_to_goals(B, G2),
    append(G1, G2, Goals).
body_to_goals(Goal, [Goal]).

contains_same_predicate_call(Term, Head) :-
    compound(Term),
    functor(Head, Name, Arity),
    (   functor(Term, Name, Arity)
    ->  true
    ;   Term =.. [_|Args],
        member(Arg, Args),
        contains_same_predicate_call(Arg, Head)
    ).

% =============================================================================
% Integer recurrence extraction
% =============================================================================

extract_integer_recurrence(Clauses, Name, 2, recurrence{
    predicate: Name/2,
    domain: integer,
    input_var: n,
    output_functor: f,
    base_cases: BaseCases,
    step: step{transform:Transform, combiner:Combiner},
    guards: Guards
}) :-
    extract_integer_base_cases(Clauses, Name, 2, BaseCases),
    BaseCases \= [],
    extract_integer_recursive_case(Clauses, Name, 2, Transform, Combiner, Guards).

extract_integer_base_cases(Clauses, Name, 2, BaseCases) :-
    findall(base_case(N0, Out0),
        ( member(Clause, Clauses),
          clause_head_body(Clause, Head, Body),
          functor(Head, Name, 2),
          arg(1, Head, N0),
          arg(2, Head, Out0),
          integer(N0),
          number(Out0),
          \+ contains_same_predicate_call(Body, Head)
        ),
        Raw),
    sort(Raw, BaseCases).

extract_integer_recursive_case(Clauses, Name, 2, Transform, Combiner, Guards) :-
    member(Clause, Clauses),
    clause_head_body(Clause, Head, Body),
    functor(Head, Name, 2),
    arg(1, Head, N),
    arg(2, Head, Out),
    var(N),
    var(Out),
    body_to_goals(Body, Goals),
    select(RecGoal, Goals, Goals1),
    compound(RecGoal),
    functor(RecGoal, Name, 2),
    arg(1, RecGoal, RecIn),
    arg(2, RecGoal, RecOut),
    extract_integer_transform(Goals1, N, RecIn, Transform, Goals2),
    extract_integer_combiner(Goals2, N, Out, RecOut, Combiner, Guards),
    !.

extract_integer_transform(Goals, N, RecIn, Transform, Rest) :-
    select(Goal, Goals, Rest),
    integer_transform_goal(Goal, N, RecIn, Transform),
    !.

integer_transform_goal((RecIn is Expr), N, RecIn, dec(1)) :-
    Expr =.. [-, A, B],
    A == N,
    B == 1,
    !.
integer_transform_goal((RecIn is Expr), N, RecIn, dec(K)) :-
    Expr =.. [-, A, B],
    A == N,
    integer(B),
    B > 0,
    K = B,
    !.
integer_transform_goal(_Goal, N, RecIn, same) :-
    RecIn == N.

extract_integer_combiner(Goals, N, Out, RecOut, Combiner, Guards) :-
    select(Goal, Goals, Guards),
    integer_combiner_goal(Goal, N, Out, RecOut, Combiner),
    !.

integer_combiner_goal((Out is Expr), N, Out, RecOut, add(current_n)) :-
    Expr =.. [+, A, B],
    ( (A == RecOut, B == N)
    ; (A == N, B == RecOut)
    ),
    !.
integer_combiner_goal((Out is Expr), _N, Out, RecOut, add(constant(C))) :-
    Expr =.. [+, A, B],
    ( (A == RecOut, number(B), C = B)
    ; (B == RecOut, number(A), C = A)
    ),
    !.
integer_combiner_goal((Out is Expr), N, Out, RecOut, multiply(current_n)) :-
    Expr =.. [*, A, B],
    ( (A == N, B == RecOut)
    ; (A == RecOut, B == N)
    ),
    !.
integer_combiner_goal((Out = RecOut), _N, Out, RecOut, identity) :-
    !.

% =============================================================================
% List recurrence extraction
% =============================================================================

extract_list_recurrence(Clauses, Name, 2, recurrence{
    predicate: Name/2,
    domain: list,
    input_var: xs,
    output_functor: f,
    base_cases: BaseCases,
    step: step{transform:tail, combiner:Combiner},
    guards: Guards
}) :-
    extract_list_base_cases(Clauses, Name, 2, BaseCases),
    BaseCases \= [],
    extract_list_recursive_case(Clauses, Name, 2, Combiner, Guards).

extract_list_base_cases(Clauses, Name, 2, BaseCases) :-
    findall(base_case([], Out0),
        ( member(Clause, Clauses),
          clause_head_body(Clause, Head, Body),
          functor(Head, Name, 2),
          arg(1, Head, []),
          arg(2, Head, Out0),
          number(Out0),
          \+ contains_same_predicate_call(Body, Head)
        ),
        Raw),
    sort(Raw, BaseCases).

extract_list_recursive_case(Clauses, Name, 2, Combiner, Guards) :-
    member(Clause, Clauses),
    clause_head_body(Clause, Head, Body),
    functor(Head, Name, 2),
    arg(1, Head, [H|T]),
    arg(2, Head, Out),
    var(T),
    var(Out),
    body_to_goals(Body, Goals),
    select(RecGoal, Goals, Goals1),
    compound(RecGoal),
    functor(RecGoal, Name, 2),
    arg(1, RecGoal, T),
    arg(2, RecGoal, RecOut),
    extract_list_combiner(Goals1, H, Out, RecOut, Combiner, Guards),
    !.

extract_list_combiner(Goals, H, Out, RecOut, Combiner, Guards) :-
    select(Goal, Goals, Guards),
    list_combiner_goal(Goal, H, Out, RecOut, Combiner),
    !.

list_combiner_goal((Out is Expr), H, Out, RecOut, add(head)) :-
    Expr =.. [+, A, B],
    ( (A == RecOut, B == H)
    ; (A == H, B == RecOut)
    ),
    !.
list_combiner_goal((Out is Expr), _H, Out, RecOut, add(constant(1))) :-
    Expr =.. [+, A, B],
    ( (A == RecOut, B == 1)
    ; (A == 1, B == RecOut)
    ),
    !.
list_combiner_goal((Out = RecOut), _H, Out, RecOut, identity) :-
    !.
    
% =============================================================================
% Closed-form derivation
% =============================================================================

derive_fallback_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: recurrence_only,
    formula: unsupported_closed_form(Recurrence),
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(output_functor, Recurrence, F).

recurrence_step(Recurrence, Transform, Combiner) :-
    get_dict(step, Recurrence, Step),
    get_dict(transform, Step, Transform),
    get_dict(combiner, Step, Combiner).

recurrence_base_case(Recurrence, In, Out) :-
    get_dict(base_cases, Recurrence, BaseCases),
    memberchk(base_case(In, Out), BaseCases).

derive_integer_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: sum_1_to_n,
    formula: (N * (N + 1) // 2),
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(input_var, Recurrence, N),
    get_dict(output_functor, Recurrence, F),
    recurrence_step(Recurrence, dec(1), add(current_n)),
    recurrence_base_case(Recurrence, 0, 0),
    !.

derive_integer_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: factorial,
    formula: factorial(N),
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(input_var, Recurrence, N),
    get_dict(output_functor, Recurrence, F),
    recurrence_step(Recurrence, dec(1), multiply(current_n)),
    recurrence_base_case(Recurrence, 0, 1),
    !.

derive_integer_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: constant_step_sum,
    formula: (B0 + N * C),
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(input_var, Recurrence, N),
    get_dict(output_functor, Recurrence, F),
    recurrence_step(Recurrence, dec(1), add(constant(C))),
    recurrence_base_case(Recurrence, 0, B0),
    number(C),
    !.

derive_integer_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: constant,
    formula: B0,
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(output_functor, Recurrence, F),
    recurrence_step(Recurrence, dec(1), identity),
    recurrence_base_case(Recurrence, 0, B0),
    !.

derive_list_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: list_length,
    formula: length_of(Xs),
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(input_var, Recurrence, Xs),
    get_dict(output_functor, Recurrence, F),
    recurrence_step(Recurrence, tail, add(constant(1))),
    recurrence_base_case(Recurrence, [], 0),
    !.

derive_list_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: list_sum,
    formula: sum_of(Xs),
    function: F
}) :-
    get_dict(predicate, Recurrence, Pred),
    get_dict(input_var, Recurrence, Xs),
    get_dict(output_functor, Recurrence, F),
    recurrence_step(Recurrence, tail, add(head)),
    recurrence_base_case(Recurrence, [], 0),
    !.

% =============================================================================
% Accumulator detection
% =============================================================================

detect_accumulator_pattern(Clauses, Name, 2, Pattern) :-
    member(WrapperClause, Clauses),
    clause_head_body(WrapperClause, WrapperHead, WrapperBody),
    functor(WrapperHead, Name, 2),
    arg(1, WrapperHead, InVar),
    arg(2, WrapperHead, OutVar),
    body_to_goals(WrapperBody, WrapperGoals),
    member(WorkerCall, WrapperGoals),
    compound(WorkerCall),
    functor(WorkerCall, WorkerName, 3),
    WorkerName \== Name,
    arg(1, WorkerCall, InVar),
    arg(2, WorkerCall, InitAcc),
    arg(3, WorkerCall, OutVar),
    member(WorkerClause, Clauses),
    clause_head_body(WorkerClause, WorkerHead, WorkerBody),
    functor(WorkerHead, WorkerName, 3),
    body_to_goals(WorkerBody, WorkerGoals),
    member(RecursiveCall, WorkerGoals),
    compound(RecursiveCall),
    functor(RecursiveCall, WorkerName, 3),
    Pattern = normalizable_tail_recursion{
        wrapper: Name/2,
        worker: WorkerName/3,
        initial_accumulator: InitAcc
    },
    !.

% =============================================================================
% Verification
% =============================================================================

verify_on_range(Clauses, Name, Arity, ClosedForm, MaxN, Report) :-
    must_be(integer, MaxN),
    MaxN >= 0,
    setup_call_cleanup(
        load_predicate_clauses_temp(Clauses, Refs),
        verify_range_loop(Name, Arity, ClosedForm, 0, MaxN, [], Mismatches),
        unload_temp_clauses(Refs)
    ),
    (   Mismatches == []
    ->  Report = verified(MaxN)
    ;   reverse(Mismatches, Ordered),
        Report = mismatches(Ordered)
    ).

verify_range_loop(_Name, _Arity, _ClosedForm, Cur, Max, Acc, Acc) :-
    Cur > Max,
    !.
verify_range_loop(Name, Arity, ClosedForm, Cur, Max, Acc, Report) :-
    eval_closed_form(ClosedForm, Cur, Expected),
    (   call_original(Name, Arity, Cur, Actual)
    ->  (   Actual =:= Expected
        ->  Acc1 = Acc
        ;   Acc1 = [mismatch(Cur, Actual, Expected)|Acc]
        )
    ;   Acc1 = [call_failed(Cur)|Acc]
    ),
    Next is Cur + 1,
    verify_range_loop(Name, Arity, ClosedForm, Next, Max, Acc1, Report).

eval_closed_form(closed_form{kind:sum_1_to_n}, N, Value) :-
    Value is (N * (N + 1)) // 2.
eval_closed_form(closed_form{kind:factorial}, N, Value) :-
    factorial_eval(N, Value).
eval_closed_form(closed_form{kind:constant_step_sum, formula:Formula}, N, Value) :-
    eval_formula(Formula, N, Value).
eval_closed_form(closed_form{kind:constant, formula:B0}, _N, B0).
eval_closed_form(closed_form{kind:recurrence_only}, _N, _) :-
    throw(error(domain_error(verifiable_closed_form, recurrence_only), _)).
eval_closed_form(closed_form{kind:list_length}, _N, _) :-
    throw(error(domain_error(verifiable_closed_form, list_length), _)).
eval_closed_form(closed_form{kind:list_sum}, _N, _) :-
    throw(error(domain_error(verifiable_closed_form, list_sum), _)).
eval_closed_form(closed_form{kind:normalizable_tail_recursion}, _N, _) :-
    throw(error(domain_error(verifiable_closed_form, normalizable_tail_recursion), _)).

factorial_eval(0, 1) :- !.
factorial_eval(N, Value) :-
    N > 0,
    N1 is N - 1,
    factorial_eval(N1, V1),
    Value is N * V1.

eval_formula((A + B), N, V) :-
    !,
    eval_formula(A, N, VA),
    eval_formula(B, N, VB),
    V is VA + VB.
eval_formula((A * B), N, V) :-
    !,
    eval_formula(A, N, VA),
    eval_formula(B, N, VB),
    V is VA * VB.
eval_formula((A // B), N, V) :-
    !,
    eval_formula(A, N, VA),
    eval_formula(B, N, VB),
    V is VA // VB.
eval_formula(n, N, N) :- !.
eval_formula(X, _N, X) :-
    number(X).

% =============================================================================
% Temporary loading
% =============================================================================

load_predicate_clauses_temp(Clauses, Refs) :-
    findall(Ref,
        ( member(Clause, Clauses),
          loadable_clause(Clause),
          assertz(user:Clause, Ref)
        ),
        Refs).

loadable_clause((:- _)) :- !, fail.
loadable_clause(_).

unload_temp_clauses([]).
unload_temp_clauses([Ref|Refs]) :-
    erase(Ref),
    unload_temp_clauses(Refs).

call_original(Name, 2, Input, Output) :-
    Goal =.. [Name, Input, Output],
    once(user:call(Goal)).

% =============================================================================
% Demo suite
% =============================================================================

run_demo :-
    writeln(''),
    writeln('=== MI Demo Suite ==='),
    writeln(''),
    demo_sum,
    demo_factorial,
    demo_length,
    demo_sumlist,
    demo_reverse_acc,
    writeln('Demo suite complete.').

demo_sum :-
    writeln('--- Demo: sum_to/2 ---'),
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :-
            N > 0,
            N1 is N - 1,
            sum_to(N1, S1),
            S is S1 + N)
    ],
    analyze_predicate(Clauses, sum_to, 2, Analysis),
    pretty_print_analysis(Analysis),
    (   get_dict(closed_form, Analysis, ClosedForm)
    ->  (   verify_on_range(Clauses, sum_to, 2, ClosedForm, 10, Report)
        ->  format("Verification: ~q~n~n", [Report])
        ;   writeln('Verification failed.'), nl
        )
    ;   nl
    ).

demo_factorial :-
    writeln('--- Demo: fact/2 ---'),
    Clauses = [
        fact(0, 1),
        (fact(N, R) :-
            N > 0,
            N1 is N - 1,
            fact(N1, R1),
            R is N * R1)
    ],
    analyze_predicate(Clauses, fact, 2, Analysis),
    pretty_print_analysis(Analysis),
    nl.

demo_length :-
    writeln('--- Demo: len/2 ---'),
    Clauses = [
        len([], 0),
        (len([_H|T], N) :-
            len(T, N1),
            N is N1 + 1)
    ],
    analyze_predicate(Clauses, len, 2, Analysis),
    pretty_print_analysis(Analysis),
    nl.

demo_sumlist :-
    writeln('--- Demo: sumlist/2 ---'),
    Clauses = [
        sumlist([], 0),
        (sumlist([H|T], S) :-
            sumlist(T, S1),
            S is S1 + H)
    ],
    analyze_predicate(Clauses, sumlist, 2, Analysis),
    pretty_print_analysis(Analysis),
    nl.

demo_reverse_acc :-
    writeln('--- Demo: rev/2 wrapper + rev_acc/3 worker ---'),
    Clauses = [
        (rev(Xs, Ys) :- rev_acc(Xs, [], Ys)),
        rev_acc([], Acc, Acc),
        (rev_acc([H|T], Acc, Ys) :-
            rev_acc(T, [H|Acc], Ys))
    ],
    analyze_predicate(Clauses, rev, 2, Analysis),
    pretty_print_analysis(Analysis),
    nl.

% =============================================================================
% Tests
% =============================================================================

:- begin_tests(mi).

test(sum_recurrence_extraction) :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :-
            N > 0,
            N1 is N - 1,
            sum_to(N1, S1),
            S is S1 + N)
    ],
    analyze_predicate(Clauses, sum_to, 2, Analysis),
    assertion(Analysis.status == supported),
    assertion(Analysis.closed_form.kind == sum_1_to_n).

test(sum_closed_form) :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :-
            N > 0,
            N1 is N - 1,
            sum_to(N1, S1),
            S is S1 + N)
    ],
    analyze_predicate(Clauses, sum_to, 2, Analysis),
    assertion(Analysis.closed_form.kind == sum_1_to_n).

test(sum_verification) :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :-
            N > 0,
            N1 is N - 1,
            sum_to(N1, S1),
            S is S1 + N)
    ],
    analyze_predicate(Clauses, sum_to, 2, Analysis),
    verify_on_range(Clauses, sum_to, 2, Analysis.closed_form, 10, Report),
    assertion(Report == verified(10)).

test(factorial_extraction) :-
    Clauses = [
        fact(0, 1),
        (fact(N, R) :-
            N > 0,
            N1 is N - 1,
            fact(N1, R1),
            R is N * R1)
    ],
    analyze_predicate(Clauses, fact, 2, Analysis),
    assertion(Analysis.closed_form.kind == factorial).

test(length_list_recurrence) :-
    Clauses = [
        len([], 0),
        (len([_H|T], N) :-
            len(T, N1),
            N is N1 + 1)
    ],
    analyze_predicate(Clauses, len, 2, Analysis),
    assertion(Analysis.closed_form.kind == list_length).

test(sumlist_list_recurrence) :-
    Clauses = [
        sumlist([], 0),
        (sumlist([H|T], S) :-
            sumlist(T, S1),
            S is S1 + H)
    ],
    analyze_predicate(Clauses, sumlist, 2, Analysis),
    assertion(Analysis.closed_form.kind == list_sum).

test(reverse_acc_detection) :-
    Clauses = [
        (rev(Xs, Ys) :- rev_acc(Xs, [], Ys)),
        rev_acc([], Acc, Acc),
        (rev_acc([H|T], Acc, Ys) :-
            rev_acc(T, [H|Acc], Ys))
    ],
    analyze_predicate(Clauses, rev, 2, Analysis),
    assertion(Analysis.closed_form.kind == normalizable_tail_recursion).

test(write_outputs) :-
    Analyses = [
        analysis{
            predicate: sum_to/2,
            status: supported,
            recurrence: recurrence{
                predicate: sum_to/2,
                domain: integer,
                input_var: n,
                output_functor: f,
                base_cases: [base_case(0,0)],
                step: step{transform:dec(1), combiner:add(current_n)},
                guards: []
            },
            closed_form: closed_form{
                predicate: sum_to/2,
                kind: sum_1_to_n,
                formula: (n * (n + 1) // 2),
                function: f
            }
        }
    ],
    with_output_to(string(S), write_rewritten_stream(current_output, Analyses)),
    once(sub_string(S, _, _, _, "sum_to")).

:- end_tests(mi).

run_mi_tests :-
    run_tests([mi]).