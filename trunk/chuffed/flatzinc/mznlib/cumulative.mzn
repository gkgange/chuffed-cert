%-----------------------------------------------------------------------------%
% Requires that a set of tasks given by start times 's', durations 'd', and
% resource requirements 'r', never require more than a global resource bound
% 'b' at any one time.
% Assumptions:
% - forall i, d[i] >= 0 and r[i] >= 0
%-----------------------------------------------------------------------------%

%predicate cumulative(array[int] of var int: s,
%                     array[int] of var int: d,
%                     array[int] of var int: r, var int: b) =
%    assert(
%        index_set(s) == index_set(d) /\ index_set(s) == index_set(r),
%        "cumulative: the 3 array arguments must have identical index sets",
%        forall(i in index_set(d))(d[i] >= 0 /\ r[i] >= 0)
%	/\  if is_fixed(d) /\ is_fixed(r) /\ is_fixed(b) then
%		    chuffed_cumulative(s, fix(d), fix(r), fix(b))
%	    else
%		    chuffed_cumulative_vars(s, d, r, b)
%	    endif
%    );

predicate cumulative(array[int] of var int: s,
                     array[int] of var int: d,
                     array[int] of var int: r, var int: b) =
    assert(index_set(s) == index_set(d) /\ index_set(s) == index_set(r),
        "cumulative: the 3 array arguments must have identical index sets",
    assert(lb_array(d) >= 0 /\ lb_array(r) >= 0,
        "cumulative: durations and resource usages must be non-negative",
%    if forall(i in index_set(r))(is_fixed(r[i]) /\ fix(r[i]) == 1) /\
%       is_fixed(b) /\ fix(b) == 1 then
%        if forall(i in index_set(d))(is_fixed(d[i]) /\ fix(d[i]) == 1) then
%            alldifferent(s)
%        else
%            disjunctive(s, d)
%        endif
%    else
	   if is_fixed(d) /\ is_fixed(r) /\ is_fixed(b) then
		    chuffed_cumulative(s, fix(d), fix(r), fix(b))
      else
        let { 
            set of int: Tasks = 
                {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0 },
            int: early = min([ lb(s[i])            | i in Tasks ]), 
            int: late  = max([ ub(s[i]) + ub(d[i]) | i in Tasks ]) 
        } in (
            if late - early > 5000 then
               cumulative_task(s, d, r, b)
            else
               cumulative_time(s, d, r, b)
            endif
        )
    endif
    ));

predicate cumulative_time(array[int] of var int: s,
                     array[int] of var int: d,
                     array[int] of var int: r, var int: b) =
    let { 
        set of int: Tasks = 
            {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0 },
        int: early = min([ lb(s[i]) | i in Tasks ]), 
        int: late  = max([ ub(s[i]) + ub(d[i]) | i in Tasks ]) 
    } in (
        forall( t in early..late ) (
            b >= sum( i in Tasks ) (
                bool2int(s[i] <= t /\ t < s[i] + d[i]) * r[i]
            )
        )
    );

predicate cumulative_task(array[int] of var int: s,
                     array[int] of var int: d,
                     array[int] of var int: r, var int: b) =
    let { 
        set of int: Tasks = 
            {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0 }
    } in (
        forall( j in Tasks ) ( 
            b >= r[j] + sum( i in Tasks where i != j ) ( 
                bool2int(s[i] <= s[j] /\ s[j] < s[i] + d[i] ) * r[i]
            )
        )
    );


%predicate cumulative_cal(array[int] of var int: s,
%                     array[int] of var int: d,
%                     array[int] of var int: r, var int: b,
%                     array[int,int] of int: cal,
%                     array[int] of int: tc, int: rho, int: resCal) =
%    let {
%        int: index1 = card(index_set_1of2(cal)),
%        int: index2 = card(index_set_2of2(cal)),
%        set of int: times = 0..index2-1
%    } in
%    assert(
%       index_set(s) == index_set(d) /\ index_set(s) == index_set(r),
%       "cumulative: the 3 array arguments must have identical index sets",
%            chuffed_cumulative_cal(s, d, r, b, index1, index2, cal, tc, rho, resCal)
%    
% %   forall( t in times ) (
%  %  b >= sum( i in index_set(s) ) (
% %   bool2int( s[i] <= t /\ t < s[i] + d[i] ) * (cal[tc[i],t+1] + (1 - cal[tc[i],t+1]) * rho)* r[i] 
% %   )
%);

	% Global cumulative propagator
	%
predicate chuffed_cumulative(array[int] of var int: s, array[int] of int: d,
	array[int] of int: r, int: b);

%predicate chuffed_cumulative_vars(array[int] of var int: s, array[int] of var int: d,
%	array[int] of var int: r, var int: b);

%predicate chuffed_cumulative_cal(array[int] of var int: s, array[int] of var int: d,
%	array[int] of var int: r, var int: b, int: index1, int: index2, array[int,int] of int: cal, array[int] of int: tc, int: rho, int: resCal);

