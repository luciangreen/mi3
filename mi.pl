:- module(mi, [
    process_file/2,                % +InputFile, +OutputBase
    analyze_file/2,                % +InputFile, -Analyses
    analyze_predicate/4,           % +Clauses, +Name, +Arity, -Analysis
    extract_recurrence/4,          % +Clauses, +Name, +Arity, -Recurrence
    derive_closed_form/2,          % +Recurrence, -ClosedForm
    verify_on_range/6,             % +Clauses, +Name, +Arity, +ClosedForm, +MaxN, -Report
    write_analysis_report/2,       % +Analyses, +File
    write_rewritten_module/2,      % +Analyses, +File
    pretty_print_analysis/1,
    run_demo/0,
    run_tests/0
]).

/** <module> mi

A recurrence-extraction architecture for a narrow but real subset of Prolog.

This module analyses clauses semantically rather than fitting traces to a
polynomial basis. It currently supports:

  * integer recursion on arity-2 predicates
  * selected direct-recursive forms over integers
  * selected list-recursive forms over arity-2 predicates
  * simple accumulator normalisation patterns for sum/reverse/length
  * bounded equivalence verification against original clauses
  * file I/O, report generation, rewritten-module emission, tests, demos

The emphasis is correctness and explainability over aggressive rewriting.
Unsupported cases are reported explicitly.
*/

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(error)).
:- use_module(library(readutil)).
:- use_module(library(plunit)).

% -----------------------------------------------------------------------------
% Public API
% -----------------------------------------------------------------------------

process_file(InputFile, OutputBase) :-
    analyze_file(InputFile, Analyses),
    atom_concat(OutputBase, '.report.txt', ReportFile),
    atom_concat(OutputBase, '.rewritten.pl', RewriteFile),
    write_analysis_report(Analyses, ReportFile),
    write_rewritten_module(Analyses, RewriteFile).

analyze_file(InputFile, Analyses) :-
    parse_file_clauses(InputFile, Clauses),
    predicate_indicators_from_clauses(Clauses, Preds0),
    sort(Preds0, Preds),
    findall(Analysis,
        (
            member(Name/Arity, Preds),
            safely_analyze_predicate(Clauses, Name, Arity, Analysis)
        ),
        Analyses).

safely_analyze_predicate(Clauses, Name, Arity, Analysis) :-
    catch(
        analyze_predicate(Clauses, Name, Arity, Analysis),
        Error,
        Analysis = analysis{
            predicate: Name/Arity,
            status: unsupported,
            reason: Error
        }
    ).

analyze_predicate(Clauses, Name, Arity, Analysis) :-
    must_be(list, Clauses),
    must_be(atom, Name),
    must_be(integer, Arity),
    partition_predicate_clauses(Clauses, Name, Arity, PredClauses),
    PredClauses \= [],
    (
        extract_recurrence(Clauses, Name, Arity, Recurrence) ->
        ( derive_closed_form(Recurrence, ClosedForm) ->
            Status = supported,
            Analysis = analysis{
                predicate: Name/Arity,
                status: Status,
                recurrence: Recurrence,
                closed_form: ClosedForm
            }
        ;
            Analysis = analysis{
                predicate: Name/Arity,
                status: partial,
                recurrence: Recurrence,
                reason: no_supported_closed_form
            }
        )
    ;
        detect_tail_accumulator_pattern(PredClauses, Name, Arity, AccInfo) ->
        Analysis = analysis{
            predicate: Name/Arity,
            status: normalizable_tail_recursion,
            accumulator_pattern: AccInfo
        }
    ;
        Analysis = analysis{
            predicate: Name/Arity,
            status: unsupported,
            reason: unsupported_recursion_shape
        }
    ).

extract_recurrence(Clauses, Name, Arity, Recurrence) :-
    partition_predicate_clauses(Clauses, Name, Arity, PredClauses),
    PredClauses \= [],
    ( extract_integer_recurrence(PredClauses, Name, Arity, Recurrence)
    ; extract_list_recurrence(PredClauses, Name, Arity, Recurrence)
    ).

% -----------------------------------------------------------------------------
% Closed-form derivation
% -----------------------------------------------------------------------------

derive_closed_form(recurrence{
    predicate: Pred,
    domain: integer,
    input_var: N,
    output_functor: F,
    base_cases: BaseCases,
    step: step{transform: dec(1), combiner: add(current_n)}
}, closed_form{
    predicate: Pred,
    kind: sum_1_to_n,
    formula: (N * (N + 1) // 2),
    function: F
}) :-
    member(base_case(0, 0), BaseCases), !.

derive_closed_form(recurrence{
    predicate: Pred,
    domain: integer,
    input_var: N,
    output_functor: F,
    base_cases: BaseCases,
    step: step{transform: dec(1), combiner: add(constant(C))}
}, closed_form{
    predicate: Pred,
    kind: constant_step_sum,
    formula: (B0 + N * C),
    function: F
}) :-
    member(base_case(0, B0), BaseCases),
    number(C), !.

derive_closed_form(recurrence{
    predicate: Pred,
    domain: integer,
    input_var: N,
    output_functor: F,
    base_cases: BaseCases,
    step: step{transform: dec(1), combiner: identity}
}, closed_form{
    predicate: Pred,
    kind: constant,
    formula: B0,
    function: F
}) :-
    member(base_case(0, B0), BaseCases), !.

derive_closed_form(recurrence{
    predicate: Pred,
    domain: integer,
    input_var: N,
    output_functor: F,
    base_cases: BaseCases,
    step: step{transform: dec(1), combiner: multiply(current_n)}
}, closed_form{
    predicate: Pred,
    kind: factorial,
    formula: factorial(N),
    function: F
}) :-
    member(base_case(0, 1), BaseCases), !.

derive_closed_form(recurrence{
    predicate: Pred,
    domain: list,
    input_var: Xs,
    output_functor: F,
    base_cases: BaseCases,
    step: step{transform: tail, combiner: add(constant(1))}
}, closed_form{
    predicate: Pred,
    kind: list_length,
    formula: length_of(Xs),
    function: F
}) :-
    member(base_case([], 0), BaseCases), !.

derive_closed_form(recurrence{
    predicate: Pred,
    domain: list,
    input_var: Xs,
    output_functor: F,
    base_cases: BaseCases,
    step: step{transform: tail, combiner: add(head)}
}, closed_form{
    predicate: Pred,
    kind: list_sum,
    formula: sum_of(Xs),
    function: F
}) :-
    member(base_case([], 0), BaseCases), !.

derive_closed_form(Recurrence, closed_form{
    predicate: Pred,
    kind: recurrence_only,
    formula: unsupported_closed_form(Recurrence),
    function: F
}) :-
    Pred = Recurrence.predicate,
    F = Recurrence.output_functor.

% -----------------------------------------------------------------------------
% Integer recurrence extraction
% -----------------------------------------------------------------------------

extract_integer_recurrence(Clauses, Name, Arity, recurrence{
    predicate: Name/Arity,
    domain: integer,
    input_var: n,
    output_functor: f,
    base_cases: BaseCases,
    step: Step,
    guards: Guards
}) :-
    Arity =:= 2,
    extract_integer_base_cases(Clauses, Name, Arity, BaseCases),
    BaseCases \= [],
    extract_integer_recursive_case(Clauses, Name, Arity, RecCase),
    Step = step{transform: RecCase.transform, combiner: RecCase.combiner},
    Guards = RecCase.guards.

extract_integer_base_cases(Clauses, Name, Arity, BaseCases) :-
    findall(base_case(NValue, OutValue),
        (
            member(Clause, Clauses),
            clause_head_body(Clause, Head, Body),
            functor(Head, Name, Arity),
            Arity =:= 2,
            arg(1, Head, NArg),
            arg(2, Head, OutArg),
            nonvar(NArg), integer(NArg),
            number(OutArg),
            body_has_no_recursive_call(Body, Head),
            NValue = NArg,
            OutValue = OutArg
        ),
        Raw),
    sort(Raw, BaseCases).

extract_integer_recursive_case(Clauses, Name, Arity, rec_case{
    input_var: NVar,
    output_var: OutVar,
    recursive_input: RecInputVar,
    recursive_output: RecOutVar,
    transform: Transform,
    combiner: Combiner,
    guards: Guards
}) :-
    member(Clause, Clauses),
    clause_head_body(Clause, Head, Body),
    functor(Head, Name, Arity),
    Arity =:= 2,
    arg(1, Head, NVar),
    arg(2, Head, OutVar),
    var(NVar), var(OutVar),
    body_to_goals(Body, Goals),
    identify_integer_recursive_case(Name, Arity, NVar, OutVar, Goals,
        RecInputVar, RecOutVar, Transform, Combiner, Guards), !.

identify_integer_recursive_case(Name, Arity, NVar, OutVar, Goals,
        RecInputVar, RecOutVar, Transform, Combiner, Guards) :-
    select_recursive_call(Goals, Name, Arity, RecInputVar, RecOutVar, Goals1),
    extract_transform(Goals1, NVar, RecInputVar, Transform, Goals2),
    extract_integer_combiner(Goals2, NVar, OutVar, RecOutVar, Combiner, Guards).

extract_integer_combiner(Goals, NVar, OutVar, RecOutVar, add(current_n), Guards) :-
    select((OutVar is RecOutVar + NVar), Goals, Guards), !.
extract_integer_combiner(Goals, NVar, OutVar, RecOutVar, add(current_n), Guards) :-
    select((OutVar is NVar + RecOutVar), Goals, Guards), !.
extract_integer_combiner(Goals, _NVar, OutVar, RecOutVar, add(constant(C)), Guards) :-
    select((OutVar is RecOutVar + C), Goals, Guards), number(C), !.
extract_integer_combiner(Goals, _NVar, OutVar, RecOutVar, add(constant(C)), Guards) :-
    select((OutVar is C + RecOutVar), Goals, Guards), number(C), !.
extract_integer_combiner(Goals, NVar, OutVar, RecOutVar, multiply(current_n), Guards) :-
    select((OutVar is NVar * RecOutVar), Goals, Guards), !.
extract_integer_combiner(Goals, NVar, OutVar, RecOutVar, multiply(current_n), Guards) :-
    select((OutVar is RecOutVar * NVar), Goals, Guards), !.
extract_integer_combiner(Goals, _NVar, OutVar, RecOutVar, identity, Guards) :-
    select((OutVar = RecOutVar), Goals, Guards), !.

% -----------------------------------------------------------------------------
% List recurrence extraction
% -----------------------------------------------------------------------------

extract_list_recurrence(Clauses, Name, Arity, recurrence{
    predicate: Name/Arity,
    domain: list,
    input_var: xs,
    output_functor: f,
    base_cases: BaseCases,
    step: Step,
    guards: Guards
}) :-
    Arity =:= 2,
    extract_list_base_cases(Clauses, Name, Arity, BaseCases),
    BaseCases \= [],
    extract_list_recursive_case(Clauses, Name, Arity, RecCase),
    Step = step{transform: RecCase.transform, combiner: RecCase.combiner},
    Guards = RecCase.guards.

extract_list_base_cases(Clauses, Name, Arity, BaseCases) :-
    findall(base_case(ListArg, OutValue),
        (
            member(Clause, Clauses),
            clause_head_body(Clause, Head, Body),
            functor(Head, Name, Arity),
            Arity =:= 2,
            arg(1, Head, ListArg),
            arg(2, Head, OutArg),
            nonvar(ListArg), ListArg == [],
            number(OutArg),
            body_has_no_recursive_call(Body, Head),
            OutValue = OutArg
        ),
        Raw),
    sort(Raw, BaseCases).

extract_list_recursive_case(Clauses, Name, Arity, rec_case{
    input_var: ListVar,
    output_var: OutVar,
    recursive_input: TailVar,
    recursive_output: RecOutVar,
    transform: tail,
    combiner: Combiner,
    guards: Guards
}) :-
    member(Clause, Clauses),
    clause_head_body(Clause, Head, Body),
    functor(Head, Name, Arity),
    Arity =:= 2,
    arg(1, Head, ListVar),
    arg(2, Head, OutVar),
    ListVar = [HeadVar|TailVar],
    var(OutVar),
    body_to_goals(Body, Goals),
    select_recursive_call(Goals, Name, Arity, TailVar, RecOutVar, Goals1),
    extract_list_combiner(Goals1, HeadVar, OutVar, RecOutVar, Combiner, Guards), !.

extract_list_combiner(Goals, _HeadVar, OutVar, RecOutVar, add(constant(1)), Guards) :-
    select((OutVar is RecOutVar + 1), Goals, Guards), !.
extract_list_combiner(Goals, _HeadVar, OutVar, RecOutVar, add(constant(1)), Guards) :-
    select((OutVar is 1 + RecOutVar), Goals, Guards), !.
extract_list_combiner(Goals, HeadVar, OutVar, RecOutVar, add(head), Guards) :-
    select((OutVar is RecOutVar + HeadVar), Goals, Guards), !.
extract_list_combiner(Goals, HeadVar, OutVar, RecOutVar, add(head), Guards) :-
    select((OutVar is HeadVar + RecOutVar), Goals, Guards), !.
extract_list_combiner(Goals, _HeadVar, OutVar, RecOutVar, identity, Guards) :-
    select((OutVar = RecOutVar), Goals, Guards), !.

% -----------------------------------------------------------------------------
% Accumulator normalisation detection
% -----------------------------------------------------------------------------

% This is intentionally a detector, not a full rewriter from tail form to recurrence.
% It recognises common arity-3 workers and reports them.

detect_tail_accumulator_pattern(Clauses, Name, Arity, acc_pattern{
    predicate: Name/Arity,
    worker: WorkerName/3,
    kind: Kind
}) :-
    member(Clause, Clauses),
    clause_head_body(Clause, Head, Body),
    functor(Head, Name, Arity),
    Body =.. [WorkerName, _, _, _],
    predicate_has_worker_pattern(Clauses, WorkerName, Kind),
    !.

detect_tail_accumulator_pattern(Clauses, Name, 3, acc_pattern{
    predicate: Name/3,
    worker: Name/3,
    kind: Kind
}) :-
    predicate_has_worker_pattern(Clauses, Name, Kind), !.

predicate_has_worker_pattern(Clauses, Name, reverse_accumulator) :-
    member((Head :- Body), Clauses),
    functor(Head, Name, 3),
    arg(1, Head, ListVar),
    arg(2, Head, AccVar),
    arg(3, Head, _OutVar),
    ListVar = [H|T],
    body_to_goals(Body, Goals),
    memberchk(NameCall, Goals),
    NameCall =.. [Name, T, [H|AccVar], _].
predicate_has_worker_pattern(Clauses, Name, sum_accumulator) :-
    member((Head :- Body), Clauses),
    functor(Head, Name, 3),
    arg(1, Head, NVar),
    arg(2, Head, AccVar),
    arg(3, Head, _OutVar),
    var(NVar), var(AccVar),
    body_to_goals(Body, Goals),
    memberchk((N1 is NVar - 1), Goals),
    memberchk((Acc1 is AccVar + NVar), Goals),
    memberchk(Call, Goals),
    Call =.. [Name, N1, Acc1, _].
predicate_has_worker_pattern(Clauses, Name, length_accumulator) :-
    member((Head :- Body), Clauses),
    functor(Head, Name, 3),
    arg(1, Head, ListVar),
    arg(2, Head, AccVar),
    arg(3, Head, _OutVar),
    ListVar = [_|T],
    body_to_goals(Body, Goals),
    memberchk((Acc1 is AccVar + 1), Goals),
    memberchk(Call, Goals),
    Call =.. [Name, T, Acc1, _].

% -----------------------------------------------------------------------------
% Verification
% -----------------------------------------------------------------------------

verify_on_range(Clauses, Name, Arity, ClosedForm, MaxN, Report) :-
    must_be(integer, MaxN),
    MaxN >= 0,
    setup_call_cleanup(
        load_predicate_clauses_temp(Clauses, Refs),
        verify_range_loop(Name, Arity, ClosedForm, 0, MaxN, [], Mismatches),
        unload_temp_clauses(Refs)
    ),
    ( Mismatches == [] -> Report = verified(MaxN)
    ; Report = mismatches(Mismatches)
    ).

verify_range_loop(_Name, _Arity, _ClosedForm, Cur, Max, Acc, Acc) :-
    Cur > Max, !.
verify_range_loop(Name, Arity, ClosedForm, Cur, Max, Acc, Report) :-
    eval_closed_form(ClosedForm, Cur, Expected),
    call_original(Name, Arity, Cur, Actual),
    ( number(Expected), number(Actual), Actual =:= Expected -> Acc1 = Acc
    ; Acc1 = [mismatch(Cur, Actual, Expected)|Acc]
    ),
    Next is Cur + 1,
    verify_range_loop(Name, Arity, ClosedForm, Next, Max, Acc1, Report).

verify_list_samples(Clauses, Name, Arity, ClosedForm, Samples, Report) :-
    setup_call_cleanup(
        load_predicate_clauses_temp(Clauses, Refs),
        verify_list_loop(Name, Arity, ClosedForm, Samples, [], Mismatches),
        unload_temp_clauses(Refs)
    ),
    ( Mismatches == [] -> Report = verified_list(Samples)
    ; Report = mismatches(Mismatches)
    ).

verify_list_loop(_Name, _Arity, _ClosedForm, [], Acc, Acc).
verify_list_loop(Name, Arity, ClosedForm, [Xs|Rest], Acc, Report) :-
    eval_closed_form(ClosedForm, Xs, Expected),
    call_original(Name, Arity, Xs, Actual),
    ( number(Expected), number(Actual), Actual =:= Expected -> Acc1 = Acc
    ; Acc1 = [mismatch(Xs, Actual, Expected)|Acc]
    ),
    verify_list_loop(Name, Arity, ClosedForm, Rest, Acc1, Report).

% -----------------------------------------------------------------------------
% File parsing and reporting
% -----------------------------------------------------------------------------

parse_file_clauses(InputFile, Clauses) :-
    setup_call_cleanup(
        open(InputFile, read, Stream),
        read_clauses_from_stream(Stream, Clauses),
        close(Stream)
    ).

read_clauses_from_stream(Stream, []) :-
    at_end_of_stream(Stream), !.
read_clauses_from_stream(Stream, Clauses) :-
    read_term(Stream, Term, []),
    ( Term == end_of_file -> Clauses = []
    ; Clauses = [Term|Rest],
      read_clauses_from_stream(Stream, Rest)
    ).

write_analysis_report(Analyses, File) :-
    setup_call_cleanup(
        open(File, write, Stream),
        write_analysis_report_stream(Stream, Analyses),
        close(Stream)
    ).

write_analysis_report_stream(Stream, Analyses) :-
    format(Stream, "MI Analysis Report~n", []),
    format(Stream, "==================~n~n", []),
    forall(member(A, Analyses), write_one_analysis_report(Stream, A)).

write_one_analysis_report(Stream, Analysis) :-
    format(Stream, "Predicate: ~w~n", [Analysis.predicate]),
    format(Stream, "Status: ~w~n", [Analysis.status]),
    ( get_dict(recurrence, Analysis, Rec) ->
        format(Stream, "Recurrence: ~q~n", [Rec]) ; true ),
    ( get_dict(closed_form, Analysis, CF) ->
        format(Stream, "Closed form: ~q~n", [CF]) ; true ),
    ( get_dict(accumulator_pattern, Analysis, Acc) ->
        format(Stream, "Accumulator pattern: ~q~n", [Acc]) ; true ),
    ( get_dict(reason, Analysis, Reason) ->
        format(Stream, "Reason: ~q~n", [Reason]) ; true ),
    nl(Stream).

write_rewritten_module(Analyses, File) :-
    setup_call_cleanup(
        open(File, write, Stream),
        write_rewritten_module_stream(Stream, Analyses),
        close(Stream)
    ).

write_rewritten_module_stream(Stream, Analyses) :-
    supported_exports(Analyses, Exports),
    format(Stream, ":- module(mi_rewritten, ~q).~n~n", [Exports]),
    format(Stream, "%% Auto-generated by mi.pl~n", []),
    format(Stream, "%% Only predicates with supported closed forms are emitted.~n~n", []),
    forall(
        ( member(A, Analyses),
          get_dict(status, A, supported),
          get_dict(closed_form, A, CF)
        ),
        write_closed_form_predicate(Stream, CF)
    ).

supported_exports(Analyses, Exports) :-
    findall(Name/Arity,
        (
            member(A, Analyses),
            get_dict(status, A, supported),
            A.predicate = Name/Arity
        ),
        Exports).

write_closed_form_predicate(Stream, closed_form{predicate: Name/2, kind: sum_1_to_n}) :-
    !,
    format(Stream, "~w(N, R) :-~n", [Name]),
    format(Stream, "    integer(N),~n", []),
    format(Stream, "    N >= 0,~n", []),
    format(Stream, "    R is (N * (N + 1)) // 2.~n~n", []).
write_closed_form_predicate(Stream, closed_form{predicate: Name/2, kind: factorial}) :-
    !,
    format(Stream, "~w(0, 1) :- !.~n", [Name]),
    format(Stream, "~w(N, R) :-~n", [Name]),
    format(Stream, "    integer(N),~n", []),
    format(Stream, "    N > 0,~n", []),
    format(Stream, "    N1 is N - 1,~n", []),
    format(Stream, "    ~w(N1, R1),~n", [Name]),
    format(Stream, "    R is N * R1.~n~n", []).
write_closed_form_predicate(Stream, closed_form{predicate: Name/2, kind: constant_step_sum, formula: (B0 + n * C)}) :-
    !,
    format(Stream, "~w(N, R) :-~n", [Name]),
    format(Stream, "    integer(N),~n", []),
    format(Stream, "    N >= 0,~n", []),
    format(Stream, "    R is ~w + N * ~w.~n~n", [B0, C]).
write_closed_form_predicate(Stream, closed_form{predicate: Name/2, kind: constant, formula: B0}) :-
    !,
    format(Stream, "~w(_N, ~w).~n~n", [Name, B0]).
write_closed_form_predicate(Stream, closed_form{predicate: Name/2, kind: list_length}) :-
    !,
    format(Stream, "~w(Xs, R) :-~n", [Name]),
    format(Stream, "    is_list(Xs),~n", []),
    format(Stream, "    length(Xs, R).~n~n", []).
write_closed_form_predicate(Stream, closed_form{predicate: Name/2, kind: list_sum}) :-
    !,
    format(Stream, "~w(Xs, R) :-~n", [Name]),
    format(Stream, "    is_list(Xs),~n", []),
    format(Stream, "    sum_list(Xs, R).~n~n", []).
write_closed_form_predicate(Stream, CF) :-
    format(Stream, "%% Unsupported emission for ~q~n~n", [CF]).

pretty_print_analysis(Analysis) :-
    format("Predicate: ~w~n", [Analysis.predicate]),
    format("Status: ~w~n", [Analysis.status]),
    ( get_dict(recurrence, Analysis, Rec) -> format("Recurrence: ~q~n", [Rec]) ; true ),
    ( get_dict(closed_form, Analysis, CF) -> format("Closed form: ~q~n", [CF]) ; true ),
    ( get_dict(accumulator_pattern, Analysis, Acc) -> format("Accumulator pattern: ~q~n", [Acc]) ; true ),
    ( get_dict(reason, Analysis, Reason) -> format("Reason: ~q~n", [Reason]) ; true ).

% -----------------------------------------------------------------------------
% Helpers
% -----------------------------------------------------------------------------

predicate_indicators_from_clauses(Clauses, Preds) :-
    findall(Name/Arity,
        (
            member(Clause, Clauses),
            clause_head_body(Clause, Head, _),
            compound(Head),
            functor(Head, Name, Arity),
            \+ predicate_indicator_to_skip(Name/Arity)
        ),
        Preds).

predicate_indicator_to_skip((:-)/1).
predicate_indicator_to_skip((?-)/1).
predicate_indicator_to_skip((,)/2).
predicate_indicator_to_skip((;)/2).
predicate_indicator_to_skip((->)/2).
predicate_indicator_to_skip(_/_) :- fail.

partition_predicate_clauses(Clauses, Name, Arity, PredClauses) :-
    include(is_target_clause(Name, Arity), Clauses, PredClauses).

is_target_clause(Name, Arity, Clause) :-
    clause_head_body(Clause, Head, _Body),
    compound(Head),
    functor(Head, Name, Arity).

clause_head_body((Head :- Body), Head, Body) :- !.
clause_head_body(Head, Head, true).

body_has_no_recursive_call(true, _Head) :- !.
body_has_no_recursive_call(Body, Head) :-
    \+ contains_same_predicate_call(Body, Head).

contains_same_predicate_call(Term, Head) :-
    compound(Term),
    functor(Head, Name, Arity),
    ( functor(Term, Name, Arity)
    ; Term =.. [_|Args],
      member(Arg, Args),
      contains_same_predicate_call(Arg, Head)
    ).

body_to_goals(true, []) :- !.
body_to_goals((A, B), Goals) :- !,
    body_to_goals(A, G1),
    body_to_goals(B, G2),
    append(G1, G2, Goals).
body_to_goals(Goal, [Goal]).

select_recursive_call(Goals, Name, Arity, RecInputVar, RecOutVar, RestGoals) :-
    select(Call, Goals, RestGoals),
    compound(Call),
    functor(Call, Name, Arity),
    Arity =:= 2,
    arg(1, Call, RecInputVar),
    arg(2, Call, RecOutVar).

extract_transform(Goals, NVar, RecInputVar, dec(1), RestGoals) :-
    select((RecInputVar is NVar - 1), Goals, RestGoals), !.
extract_transform(Goals, NVar, RecInputVar, dec(K), RestGoals) :-
    select((RecInputVar is NVar - K), Goals, RestGoals),
    integer(K), K > 0, !.
extract_transform(Goals, NVar, RecInputVar, same, Goals) :-
    RecInputVar == NVar.

% -----------------------------------------------------------------------------
% Evaluation of closed forms
% -----------------------------------------------------------------------------

eval_closed_form(closed_form{kind: sum_1_to_n}, N, Value) :-
    integer(N),
    Value is (N * (N + 1)) // 2.
eval_closed_form(closed_form{kind: constant_step_sum, formula: Formula}, N, Value) :-
    integer(N),
    eval_formula(Formula, N, Value).
eval_closed_form(closed_form{kind: constant, formula: B0}, _N, B0) :-
    number(B0).
eval_closed_form(closed_form{kind: factorial}, N, Value) :-
    integer(N),
    factorial_eval(N, Value).
eval_closed_form(closed_form{kind: list_length}, Xs, Value) :-
    is_list(Xs),
    length(Xs, Value).
eval_closed_form(closed_form{kind: list_sum}, Xs, Value) :-
    is_list(Xs),
    sum_list(Xs, Value).
eval_closed_form(closed_form{kind: recurrence_only}, _Input, _) :-
    throw(error(domain_error(verifiable_closed_form, recurrence_only), _)).

factorial_eval(0, 1) :- !.
factorial_eval(N, Value) :-
    N > 0,
    N1 is N - 1,
    factorial_eval(N1, V1),
    Value is N * V1.

eval_formula((A + B), N, V) :- !,
    eval_formula(A, N, VA),
    eval_formula(B, N, VB),
    V is VA + VB.
eval_formula((A * B), N, V) :- !,
    eval_formula(A, N, VA),
    eval_formula(B, N, VB),
    V is VA * VB.
eval_formula((A // B), N, V) :- !,
    eval_formula(A, N, VA),
    eval_formula(B, N, VB),
    V is VA // VB.
eval_formula(n, N, N) :- !.
eval_formula(X, _N, X) :- number(X).

call_original(Name, Arity, Input, Output) :-
    Arity =:= 2,
    Goal =.. [Name, Input, Output],
    call(Goal).

% -----------------------------------------------------------------------------
% Temporary loading for verification
% -----------------------------------------------------------------------------

load_predicate_clauses_temp(Clauses, Refs) :-
    include(is_loadable_clause, Clauses, Loadable),
    findall(Ref,
        ( member(Clause, Loadable), assertz(user:Clause, Ref) ),
        Refs).

is_loadable_clause((:- _)) :- !, fail.
is_loadable_clause((?- _)) :- !, fail.
is_loadable_clause(_).

unload_temp_clauses([]).
unload_temp_clauses([Ref|Refs]) :- erase(Ref), unload_temp_clauses(Refs).

% -----------------------------------------------------------------------------
% Demo suite
% -----------------------------------------------------------------------------

run_demo :-
    format("~n=== MI Demo Suite ===~n~n", []),
    demo_sum,
    demo_factorial,
    demo_list_length,
    demo_list_sum,
    demo_reverse_acc,
    format("~nAll demos complete.~n", []).

demo_sum :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :- N > 0, N1 is N - 1, sum_to(N1, S1), S is S1 + N)
    ],
    format("--- Demo: sum_to/2 ---~n", []),
    analyze_predicate(Clauses, sum_to, 2, Analysis),
    pretty_print_analysis(Analysis),
    verify_on_range(Clauses, sum_to, 2, Analysis.closed_form, 10, Report),
    format("Verification: ~q~n~n", [Report]).

demo_factorial :-
    Clauses = [
        fact(0, 1),
        (fact(N, R) :- N > 0, N1 is N - 1, fact(N1, R1), R is N * R1)
    ],
    format("--- Demo: fact/2 ---~n", []),
    analyze_predicate(Clauses, fact, 2, Analysis),
    pretty_print_analysis(Analysis),
    verify_on_range(Clauses, fact, 2, Analysis.closed_form, 7, Report),
    format("Verification: ~q~n~n", [Report]).

demo_list_length :-
    Clauses = [
        len([], 0),
        (len([_|T], N) :- len(T, N1), N is N1 + 1)
    ],
    format("--- Demo: len/2 ---~n", []),
    analyze_predicate(Clauses, len, 2, Analysis),
    pretty_print_analysis(Analysis),
    Samples = [[], [a], [a,b], [1,2,3,4]],
    verify_list_samples(Clauses, len, 2, Analysis.closed_form, Samples, Report),
    format("Verification: ~q~n~n", [Report]).

demo_list_sum :-
    Clauses = [
        sumlist([], 0),
        (sumlist([H|T], S) :- sumlist(T, S1), S is S1 + H)
    ],
    format("--- Demo: sumlist/2 ---~n", []),
    analyze_predicate(Clauses, sumlist, 2, Analysis),
    pretty_print_analysis(Analysis),
    Samples = [[], [1], [1,2], [2,4,6]],
    verify_list_samples(Clauses, sumlist, 2, Analysis.closed_form, Samples, Report),
    format("Verification: ~q~n~n", [Report]).

demo_reverse_acc :-
    Clauses = [
        (rev(Xs, Ys) :- rev_acc(Xs, [], Ys)),
        rev_acc([], Acc, Acc),
        (rev_acc([H|T], Acc, Ys) :- rev_acc(T, [H|Acc], Ys))
    ],
    format("--- Demo: reverse accumulator detection ---~n", []),
    analyze_predicate(Clauses, rev, 2, Analysis),
    pretty_print_analysis(Analysis), nl.

% -----------------------------------------------------------------------------
% Tests
% -----------------------------------------------------------------------------

run_tests :-
    run_tests([mi]).

:- begin_tests(mi).

test(sum_recurrence_extraction) :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :- N > 0, N1 is N - 1, sum_to(N1, S1), S is S1 + N)
    ],
    extract_recurrence(Clauses, sum_to, 2, Rec),
    assertion(Rec.domain = integer),
    assertion(Rec.step.transform = dec(1)),
    assertion(Rec.step.combiner = add(current_n)).

test(sum_closed_form) :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :- N > 0, N1 is N - 1, sum_to(N1, S1), S is S1 + N)
    ],
    analyze_predicate(Clauses, sum_to, 2, A),
    assertion(A.closed_form.kind = sum_1_to_n).

test(sum_verification) :-
    Clauses = [
        sum_to(0, 0),
        (sum_to(N, S) :- N > 0, N1 is N - 1, sum_to(N1, S1), S is S1 + N)
    ],
    analyze_predicate(Clauses, sum_to, 2, A),
    verify_on_range(Clauses, sum_to, 2, A.closed_form, 12, Report),
    assertion(Report = verified(12)).

test(factorial_extraction) :-
    Clauses = [
        fact(0, 1),
        (fact(N, R) :- N > 0, N1 is N - 1, fact(N1, R1), R is N * R1)
    ],
    analyze_predicate(Clauses, fact, 2, A),
    assertion(A.closed_form.kind = factorial).

test(length_list_recurrence) :-
    Clauses = [
        len([], 0),
        (len([_|T], N) :- len(T, N1), N is N1 + 1)
    ],
    analyze_predicate(Clauses, len, 2, A),
    assertion(A.closed_form.kind = list_length).

test(sumlist_list_recurrence) :-
    Clauses = [
        sumlist([], 0),
        (sumlist([H|T], S) :- sumlist(T, S1), S is S1 + H)
    ],
    analyze_predicate(Clauses, sumlist, 2, A),
    assertion(A.closed_form.kind = list_sum).

test(reverse_acc_detection) :-
    Clauses = [
        (rev(Xs, Ys) :- rev_acc(Xs, [], Ys)),
        rev_acc([], Acc, Acc),
        (rev_acc([H|T], Acc, Ys) :- rev_acc(T, [H|Acc], Ys))
    ],
    analyze_predicate(Clauses, rev, 2, A),
    assertion(A.status = normalizable_tail_recursion),
    assertion(A.accumulator_pattern.kind = reverse_accumulator).

test(write_outputs, [setup(tmp_file_stream(text, Report, S1)), cleanup((close(S1), delete_file(Report), delete_file(Rewrite)))]) :-
    close(S1),
    atom_concat(Report, '.pl', Rewrite),
    Analyses = [
        analysis{predicate:sum_to/2,status:supported,
                 recurrence:recurrence{predicate:sum_to/2,domain:integer,input_var:n,output_functor:f,base_cases:[base_case(0,0)],step:step{transform:dec(1),combiner:add(current_n)},guards:[]},
                 closed_form:closed_form{predicate:sum_to/2,kind:sum_1_to_n,formula:(n*(n+1)//2),function:f}}
    ],
    write_analysis_report(Analyses, Report),
    write_rewritten_module(Analyses, Rewrite),
    exists_file(Report),
    exists_file(Rewrite).

:- end_tests(mi).
