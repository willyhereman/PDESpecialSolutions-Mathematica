(* FINAL VERSION *)
(* ************************************************************************ *)
(* : Title : PDESpecialSolutions.m 
*  : Authors : Douglas Baldwin, Unal Goktas, and Willy Hereman.
*    Department of Mathematical and Computer Sciences
*    Colorado School of Mines
*    Golden, Colorado 80401-1887, U.S.A
*    Contact email: whereman@mines.edu

*  : Last updated : 05-13-2002 at 23:20 by Hereman.
*  : Summary : Solves systems of nonlinear PDEs in terms of the hyperbolic
*    functions Tanh, Sech, and combinations of Sech and Tanh.
*  : Also computes exact solutions in terms of the Jacobi elliptic Cn and Sn 
     functions.
*  : Warnings : This package uses the assumption that Sqrt[a^2] -> a, etc.
*    (see mySimplificationRules below) when simplifying. *)

(* ************************************************************************ *)

(* Algorithms and implementation by Douglas Baldwin, *)
(* Unal Goktas (WRI) and Willy Hereman. *)
(* Copyright 2001 *)

BeginPackage["Calculus`PDESpecialSolutions`"]

Unprotect[PDESpecialSolutions]

PDESpecialSolutions::usage = 
"PDESpecialSolutions[eqns, funcs, vars, params, opts] solves a system of
nonlinear partial differential equations (PDEs) for funcs, with
independent variables vars and non-zero parameters params. 
\[NewLine]PDESpecialSolutions takes the option Form with the default 
value Tanh. Other options include Tanh, Sech, SechTanh, Cn, and Sn.
\[NewLine]PDESpecialSolutions also takes the options NumericTest and 
SymbolicTest with the default values False. If NumericTest is set to True, 
PDESpecialSolutions tests the possible solutions based on 13 different sets of 
random numbers ranging from zero to one for all parameters and 
remaining constants. Solutions are accepted if they pass one or more of 
these tests.
\[NewLine]If SymbolicTest is set to True the solutions are tested truly
symbolically and the result of the test is shown in factored form. 
\[NewLine]In addition, PDESpecialSolutions has the option InputForm with 
the default value True. If InputForm is set to False, the output of 
PDESpecialSolutions will be in standard Mathematica output form."

PDESpecialSolutions::poly = "This system must be a polynomial of fixed order."

PDESpecialSolutions::form = "The user entered form is not valid."

PDESpecialSolutionsmSolver::freedom = "Freedom exists in this system, as `1` 
are both dominant powers in expression `2`."

PDESpecialSolutionsmSolver::noSoln = "mSolver did not find any positive 
integer values for the dominate behavior, and will now test the values from 
1 to 3 to see if the package missed a solution due to inequalities."

PDESpecialSolutionsmSolver::fail = "The algorithm failed while attempting to 
find the positive integer values of m[n]."

PDESpecialSolutions::solve = "The algorithm failed while attempting to find 
the coefficients for the polynomial solution."

(* Options definition. *)

Options[PDESpecialSolutions] =
  { Verbose -> True, 
    Form -> tanh, 
    NumericTest -> False, SymbolicTest -> False, 
    InputForm -> False, 
    DegreeOfThePolynomial -> {},
    HighestOrderFirst -> False 
  };

sech=.; sechtanh=.; cn=.; sn=.; jacobisn=.; jacobicn=.;

Begin["`Private`"]

(* If called with non-lists, makes them lists. *)

PDESpecialSolutions[eqns_?(!ListQ[#]&), funcs_, vars_, param_, 
  opts___?OptionQ]:=
  PDESpecialSolutions[{eqns}, funcs, vars, param, opts]

PDESpecialSolutions[eqns_, funcs_?(!ListQ[#]&), vars_, param_, 
  opts___?OptionQ]:=
  PDESpecialSolutions[eqns, {funcs}, vars, param, opts]

PDESpecialSolutions[eqns_, funcs_, vars_?(!ListQ[#]&), param_, 
  opts___?OptionQ]:=
  PDESpecialSolutions[eqns, funcs, {vars}, param, opts]

PDESpecialSolutions[eqns_, funcs_, vars_, param_?(!ListQ[#]&), 
  opts___?OptionQ]:=
  PDESpecialSolutions[eqns, funcs, vars, {param}, opts]

(* ************************************************************************ *)

(* Start of function PDESpecialSolutions. *)

PDESpecialSolutions[eqns_List, funcs_List, vars_List, param_List, 
  opts___?OptionQ]:=
  Block[
    {testarg = FreeQ[MapAll[Expand, eqns], (Power[b__, a__] /; 
         (!FreeQ[a, _Symbol] | MemberQ[b, _Real | _Integer]))],
     theForm =
       ToExpression[
         ToLowerCase[
           ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
         ]
       ] /. {jacobisn -> sn, jacobicn -> cn},
     VerboseTest = Verbose /. {opts} /. Options[PDESpecialSolutions],
     time = TimeUsed[],
     system,
     mSoln,
     newSystem,
     solution
    }, (* Protected Local Variables *)

  If[!testarg, Message[PDESpecialSolutions::poly]];
  (
    (* If verbose, prints system. *)
    If[VerboseTest,
      Print["The given system of differential equations is: "];
      Print[
        TableForm[eqns /. 
          {Derivative[n__][F_][x__]:>
            SequenceForm[F,
              Subscript[SequenceForm @@ 
                Flatten[
                  Table[#[[1]], {#[[2]]}
                  ]& /@ Transpose[{{x}, {n}}]
                ]
              ]
            ],
            Sequence @@ ((#->Head[#])& /@ funcs)
          }
        ]
      ]
    ];

    (* Step 1 in the paper. *)
    (* Transforms the PDE into a nonlinear ODE in $T=Tanh$ or $S=Sech$ *)
    If[VerboseTest,
      Print["Transform the differential equation(s) into a nonlinear ODE in "<>
        ToString[
          (theForm /. 
            {tanh -> "T=Tanh", sech -> "S=Sech", sechtanh -> "S=Sech", 
             cn -> "CN=JacobiCN", sn -> "SN=JacobiSN"}
          )
        ]
      ]
    ];

    system = 
    PDESpecialSolutionsVarChange[eqns /. (a__==b__):>(a-b), funcs, vars, opts];

    If[VerboseTest,
      Print[CleanUpFunction[system /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step 2 in the paper. *)
    (* Determines the maximal degree of the polynomial solutions. *)
    If[VerboseTest,
      Print["Determine the maximal degree of the polynomial solutions."]
    ];

    mSoln =
      Internal`DeactivateMessages[
        PDESpecialSolutionsmSolver[system, theForm, opts], 
        Solve::svars
      ];
    If[Length[mSoln] === 0,
      Message[PDESpecialSolutionsmSolver::fail];Abort[]
    ];

    If[VerboseTest,
      Print[
        CleanUpFunction[
          DeleteCases[mSoln,
            max[_]->_,
            2]
        ]
      ];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step 3 in the paper. *)
    (* Derives the algebraic system for the coefficients $a_{ij}, b_{ij}$. *)
    If[VerboseTest,
      Print["Derive the nonlinear algebraic system for the coefficients."]
    ];

    newSystem = 
      PDESpecialSolutionsBuildSystem[mSoln, system, vars, param, opts];

    If[VerboseTest,
      Print["The nonlinear algebraic system is"];
      Print[CleanUpFunction[newSystem /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step 4 in the paper. *)
    (* Solve the nonlinear parameterized algebraic system. *)
    If[VerboseTest,
      Print["Solve the nonlinear algebraic system."]
    ];

    solution = 
        Algebra`AnalyzeAndSolve`AnalyzeAndSolve @@ #& /@ newSystem;
    If[Length[Flatten[solution]] === 0,
      Message[PDESpecialSolutions::solve];Abort[]
    ];

    (* Reformat the output after Unal's change of AnalyzeAndSolve's output *)
    (* by Douglas Baldwin on 11/27/2002 *)
    solution = 
      (# /. List[(a_List)..] :> a)& /@ #& /@ solution; 

    If[VerboseTest,
      Print[CleanUpFunction[solution]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step 5 in the paper. *)
    (* Build and test the solitary wave solutions. *)
    If[VerboseTest,
      If[( !(NumericTest /. {opts} /. Options[PDESpecialSolutions]) &&
           !(SymbolicTest /. {opts} /. Options[PDESpecialSolutions]) ), 
        Print["Build the travelling wave solutions."],
    Print["Build and (numerically and/or symbolically) test the solutions."];
      ]
    ];

    solution = 
      PDESpecialSolutionsBuildSolutions[solution, mSoln, 
        eqns, funcs, vars, param, opts];

    If[VerboseTest,
      Print["Time Used:", TimeUsed[]-time];
      Print[];
      If[( (NumericTest /. {opts} /. Options[PDESpecialSolutions]) || 
           (SymbolicTest /. {opts} /. Options[PDESpecialSolutions]) ),
        Print["The (numerically and/or symbolically) tested final solutions:"],
        Print["The list of possible solutions is:"]
      ];
    ];

    (* Returns solutions to user. *)
    Return[
      If[InputForm /. {opts} /. Options[PDESpecialSolutions], 
        InputForm[CleanUpFunction[solution]],
        CleanUpFunction[solution]
      ]
    ]
  ) /; testarg
  ]

(* ************************************************************************ *)

(* : Title : PDESpecialSolutionsVarChange *)
(* : Author : Douglas Baldwin *)
(* : Input : The equation list (F[i][x,y,z,t]) and the form tanh. *)
(* : Output : The system in the form u[i][T] depending on whether 
     it is tanh. *)
(* : Summary : Converts from real space-time domain to u[i][T]. *)

PDESpecialSolutionsVarChange[eqns_List, funcs_List, vars_List,
    opts___?OptionQ]:=
    Block[{Form, (* The form of the wanted solution. *)
        funcRules, (* conversion from user functions *)
        i=0, (* Iterator for myTrackingVariables *)
        eqList, (* The list of equations, in a usable form *)
        system, (* The system after transformation to ODE in T *)
        phi (* A temporary function. *)
        }, (* Protected Local Variables *)

     (* Sets the Form from user options *)
     Form =
       ToExpression[
         ToLowerCase[
           ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
         ]
       ] /. {jacobisn -> sn, jacobicn -> cn};

    (* If form isn't correct, it sends a message and aborts. *)
    If[!(Or @@ ((Form === #)& /@ {tanh, sech, sechtanh, cn, sn})),
      Message[PDESpecialSolutions::form]; Abort[]
    ];

    (* Creates a set of rules to converts the users functions *)
    (* (e.g., u[n,t]) to varChangeFunction[i][n,t]. *)
    funcRules = 
      Table[
        Head[funcs[[i]] ] -> varChangeFunction[Form][i],
        {i, Length[funcs]}
      ];

    (* Adds tacking variables which will be used in the mSolve *)
    (* function to check for false balances coming form a single *)
    (* term. *)
    eqList = 
      If[Head[#] === Plus, 
        Plus @@ ((myTrackingVariable[++i]*#) & /@ List @@ #),
        myTrackingVariable[++i]*#] & /@ Expand[eqns];

    (* Converts the user functions to varChangeFunction[i]. *)
    eqList = eqList //. funcRules;

    (* Changes the space of the functions. *)
    system = eqList /. 
      {
      varChangeFunction[form_][n_][var__] :> 
        phi[form][n][
          Sum[c[i]*{var}[[i]], 
            {i, Length[{var}]}
          ]
        ], 
       Derivative[temp__][varChangeFunction[form_][n_]][var__] :>  
         (
           D[
            phi[form][n][
              Sum[c[i]*{var}[[i]], 
                {i, Length[{var}]}
              ]
            ],
            Sequence @@ Transpose[{{var}, {temp}}]
           ]
         )
      };

    (* Parameterizes the sequence $c_1 x+c_2 y+\dots\to\eta$ *)
    system = system /. 
      {
        phi[form_][n_][__] :> phi[form][n][eta],
        Derivative[i_][phi[form_][n_]][__] :> Derivative[i][phi[form][n]][eta]
      };

    (* Repeatedly applies the chain rule. *)
      system = system /. 
        {Derivative[a_][phi[tanh][n_]][eta] :> 
          Expand[
            Nest[(1-T^2)*D[#, T]&, 
              u[n][T], 
              a
            ]
          ], 
         phi[tanh][n_][eta] :> u[n][T],
         Derivative[a_][phi[sech][n_]][eta] :> 
            Expand[
              Nest[-(S*Sqrt[1-S^2])*D[#, S]&, 
                u[n][S], 
                a
              ]
            ], 
         phi[sech][n_][eta] :> u[n][S],
         Derivative[a_][phi[sechtanh][n_]][eta] :> 
            Expand[
              Nest[-(S*Sqrt[1-S^2])*D[#, S]&, 
                u[n][S], 
                a
              ]
            ], 
         phi[sechtanh][n_][eta] :> u[n][S],
         Derivative[a_][phi[cn][n_]][eta] :> 
            Expand[
              Nest[-Sqrt[1-mod-CN^2+2*mod*CN^2-mod*CN^4]*D[#, CN]&, 
                u[n][CN], 
                a
              ]
            ], 
         phi[cn][n_][eta] :> u[n][CN],
         Derivative[a_][phi[sn][n_]][eta] :> 
            Expand[
              Nest[Sqrt[1-SN^2-mod*SN^2+mod*SN^4]*D[#, SN]&, 
                u[n][SN], 
                a
              ]
            ], 
        phi[sn][n_][eta] :> u[n][SN]
        };

    system = MapAll[Expand, system];

    (* Simplifies the system by removing extra (1-T^2)'s *)
    (* and T's from the system. *)
    system = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Factor[#/(1-T^2)], Factor[#]]& /@ system;
    system = 
      If[(# /. T -> 0) === 0, 
        Factor[#/T], Factor[#]]& /@ system;
    system = 
      If[(# /. S -> 0) === 0, 
        Factor[#/S], Factor[#]]& /@ system;
    system = 
      If[(# /. S -> -1) === 0 && (# /. S->1) === 0, 
        Factor[#/Sqrt[1-S^2]], Factor[#]]& /@ system;
    system = 
      If[(# /. CN -> 0) === 0, 
        Factor[#/CN], Factor[#]]& /@ system;
    system = 
      If[(((# /. CN -> -1) === 0 && (# /. CN -> 1) === 0 ) &&
           (Factor[# /. CN -> Sqrt[-1+mod]/Sqrt[mod] ]) === 0), 
        Factor[#/Sqrt[1-mod-CN^2+2*mod*CN^2-mod*CN^4]], Factor[#]]& /@ system;
    system = 
      If[(# /. SN -> 0) === 0, 
        Factor[#/SN], Factor[#]]& /@ system;
    system = 
      If[(((# /. SN -> -1) === 0 && (# /. SN -> 1) === 0 ) &&
           (Factor[# /. SN -> 1/Sqrt[mod] ]) === 0 ), 
        Factor[#/Sqrt[1-SN^2-mod*SN^2+mod*SN^4]], Factor[#]]& /@ system;

    (* Returns the system back to the PDESpecialSolutionsr *)
    Return[MapAll[Factor, system]];
  ];

(* ************************************************************************ *)

(* : Title : PDESpecialSolutionsmSolver *)
(* : Author : Douglas Baldwin *)
(* : Date : Sunday, December 15, 2002 *)
(* : Input : The system generated by varChange. *)
(* : Output : The power of the polynomial solutions for u[i][T], id est 
     u[i][T] = a[1,0]+a[1,1]*T+a[1, 2]*T^2+...+a[1,n]*T^n. *)

PDESpecialSolutionsmSolver[system_List, theForm_, opts___?OptionQ] :=
  Module[{mSolverDebug = False, (* Debugging bool flag *)
          myTrackingVariableMax, (* Max Tracking Variable. *)
          funcRules, (* Replaces F with T, S, CN, SN, etc. *)
          eqnList, (* The result of the system generation func. *)
          mList0, mList, (* Lists of the powers of F in m_i. *)
          myMList, (* List of m_i's:  {m_1, m_2, m_3, ...} *)
          mRules, (* Rules for m_i, such as m_1 -> m_2. *)
          mSoln (* List of explicit solutions for m_i. *)
         },

    (* Determines max{i : myTrackingVariables[i]} by *)
    (* applying a rule to system which sets myTrackingVariable *)
    (* in the process.  *)
    myTrackingVariableMax = 0;
    system /. myTrackingVariable[a_Integer] :> 
      myTrackingVariable[
        If[a > myTrackingVariableMax, 
           myTrackingVariableMax = a
          ]; 
      a];

    (* Sets up a list of rules for replacing the form of F. *)
    funcRules = {tanh -> T, sech -> S, sechtanh -> S, cn -> CN, sn -> SN};

    (* Breaks into parts P + Q Sqrt[...] and substitutes *)
    (* the ansatz \chi F^{m_i} for u,v,...,w *)
    eqnList = 
      mSolve`SystemGeneration[system, theForm, myTrackingVariableMax];

    If[mSolverDebug,
      Print["eqnList, System after ansatz substitution:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Pulls off the expressions for m_i *)
    mList0 = mSolve`ListFormation[eqnList, theForm, 
                 funcRules, myTrackingVariableMax];

    If[mSolverDebug,
      Print["mList0, Exponents of F before simplification:"];
      Print[CleanUpFunction[mList0]];
    ];

    (* If the form is of SechTanh, it uses the solution m_i=2, n_i=1 *)
    If[theForm === sechtanh,
      (* Sets mSoln so m_i = 2 and n_i = 1 *)
      mSoln = 
        {
          Flatten[
            Table[{m[i]->2, n[i]->1}, 
              {i, Length[system]}
            ]
          ]
        };
      (* Appends the maximum power on an equation basis. *)
      mSoln = 
        Table[
          Join[mSoln[[j]], 
            Table[max[i]->(Max[mList0[[i]] /. mSoln[[j]] ]), 
              {i, Length[system]}
            ]
          ],
          {j, Length[mSoln]}
        ];

      (* Returns the solution. *)
      Return[mSoln];
    ];

    (* Removes expressions which cannot be the highest power *)
    (* by trackingVariable. *)
    mList = 
      Flatten[mSolve`Simplification /@ #]& /@ mList0;

    If[mSolverDebug,
      Print["mList, mList0 after simplification:"];
      Print[CleanUpFunction[mList]];
    ];

    (* Forms a list of all the m_i. *)
    myMList = {};
    mList /. 
      m[i_Integer] :> (myMList = Append[myMList, m[i]];m[i]);
    myMList = Union[myMList];

    If[mSolverDebug,
      Print["The $m_i$s to be solved for are:"];
      Print[CleanUpFunction[myMList]];
    ];

    (* Solves the expressions of m_i for m_i *)
    mRules = mSolve`RulesSolver[#, myMList]& /@ mList;

    If[mSolverDebug,
      Print["mRules, the solution iteration yields:"];
      Print[CleanUpFunction[mRules]];
    ];  

    (* Uses the previous results to determine *)
    (* explicit solutions for m_i. *)
    mSoln = mSolve`PowerSolver[mRules, myMList];

    If[mSolverDebug,
      Print["mSoln, the possible solutions before pruning:"];
      Print[CleanUpFunction[mSoln]];
    ];  

   (* If the user wants to continue with their own values. *)
   If[(DegreeOfThePolynomial /. {opts} /. Options[PDESpecialSolutions]) =!= {},
      Print["The software computed the following highest exponents: "];
      Print[CleanUpFunction[mSoln]]; 
      (* wipe out the original mSoln *)
      mSoln = {};
      mSoln = 
        Append[mSoln, 
          ToExpression[
            StringReplace[            
              ToString[DegreeOfThePolynomial /. {opts}],
              {"m" -> "Calculus`PDESpecialSolutions`Private`m",
               "n" -> "Calculus`PDESpecialSolutions`Private`n"
              }
            ]
          ]
        ]; (* end append *)
      Print["Software continues with the user given DegreeOfThePolynomial:"];
      Print[CleanUpFunction[mSoln]]
    ];

    (* Remove bad solutions. *)
    mSoln  = 
      mSolve`SystemCleanUp[eqnList, mList, mSoln, 
                          myMList, theForm /. funcRules ];

    If[mSolverDebug,
      Print["mSoln, after being pruned:"];
      Print[CleanUpFunction[mSoln]];
    ];  

    (* DB:1/12/2003 added If statement around FreeSolutions for single equations. *)
    If[ Length[myMList] > 1,
      (* DB 11/20/2002 insert new function to deal with free variables. *)
      (* Appends additional solutions in case of freedom. *)
      mSoln = 
        mSolve`FreeSolutions[mSoln,mList0];

      (* Remove bad solutions. *)
      mSoln  = 
        mSolve`SystemCleanUp[eqnList, mList, mSoln, 
                            myMList, theForm /. funcRules ];

      If[mSolverDebug,
        Print["mSoln, after adding free solutions and pruning:"];
        Print[CleanUpFunction[mSoln]];
      ];
    ];

    (* If it doesn't find any find any solutions, it quits. *)
    If[Length[mSoln] == 0, 
      Message[PDESpecialSolutionsmSolver::fail]; 
      Abort[ ]
    ];

    (* Appends the maximum value of m_i. *)
    mSoln = 
      Table[
        Join[mSoln[[j]], 
          Table[max[i]->(Max[mList0[[i]] /. mSoln[[j]] ]), 
            {i, Length[system]}
          ]
        ],
        {j, Length[mSoln]}
      ];

    If[mSolverDebug,
      Print["mSoln, the final version before being returned:"];
      Print[CleanUpFunction[mSoln]];
    ];  

    (* Returns the solutions. *)
    Return[mSoln];

  ];

(* Breaks up the system into the correct form. *)
mSolve`SystemGeneration[system_, theForm_, myTrackingVariableMax_] :=
  Block[{SystemGenerationDebug = False,
          sqrtRules, (* A set of rules for replacing what's *)
                     (* under the radical. *)
          mySystem, (* The system passed to the function after *)
                    (* transformation. *)
          eqnList (* The result which will be returned. *)
         },

    (* Sets up the way in which the system will be divided up *)
    (* in the next step, based on the Options set by the user. *)
    sqrtRules = 
      {tanh -> Null, 
       sech -> 1-S^2, 
       sechtanh -> 1-S^2,
       cn -> 1-mod-CN^2+2*mod*CN^2-mod*CN^4,
       sn -> 1-SN^2-mod*SN^2+mod*SN^4
      };

    (* Breaks up system into P and Q, where system = P + Sqrt[...]*Q. *)
    mySystem = 
      {Coefficient[#,Sqrt[theForm /. sqrtRules],0]& /@ MapAll[Expand, system], 
       Coefficient[#,Sqrt[theForm /. sqrtRules],1]& /@ MapAll[Expand, system]};

    If[SystemGenerationDebug,
      Print["The system divided into P and Q, is: "];
      Print[CleanUpFunction[mySystem]];
    ];

    mySystem = mSolve`SimplifySystem[mySystem];

    If[SystemGenerationDebug,
      Print["The system after simplification is: "];
      Print[CleanUpFunction[mySystem]];
    ];

    (* Replaces the function u[i_] with a function in *)
    (* F^m[i] or F^n[i]. *)
    eqnList = 
      Expand[
        DeleteCases[
          Flatten[
            mySystem /. u[i_] :> Function[{F}, \[Chi][i]*F^m[i] ]
          ], 
          0
        ]
      ];

    If[SystemGenerationDebug,
      Print["The system after substitution of $\chi F^{m_i}$"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Returns the list after substitution of the ansatz. *)
    Return[eqnList];

  ];


(* Simplifies the system by removing extra (1-T^2), (1-S^2), *)
(* S, T, etc. from the system. *)
mSolve`SimplifySystem[system_]:=
  Module[{mySystem = system},
    mySystem = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Expand[#/(1-T^2)], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. T->0) === 0, 
        Expand[#/T], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. S->0) === 0, 
        Expand[#/S], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. S->-1) === 0 && (# /. S->1) === 0, 
        Expand[#/Sqrt[1-S^2]], Expand[#]]& /@ #& /@ mySystem;
    mySystem = 
      If[(# /. CN -> 0) === 0, 
        Expand[#/CN], Expand[#]]& /@ mySystem;
    mySystem = 
      If[(((# /. CN -> -1) === 0 && (# /. CN -> 1) === 0 ) &&
           (Expand[# /. CN -> Sqrt[(-1+mod)/mod] ]) === 0 ), 
      Expand[#/Sqrt[1-mod-CN^2+2*mod*CN^2-mod*CN^4]], Expand[#]]& /@ mySystem;
    mySystem = 
      If[(# /. SN->0) === 0, 
        Expand[#/SN], Expand[#]]& /@ mySystem;
    mySystem = 
      If[(((# /. SN->-1) === 0 && (# /. SN->1) === 0 ) &&
           (Expand[# /. SN -> 1/Sqrt[mod] ]) === 0 ), 
        Expand[#/Sqrt[1-SN^2-mod*SN^2+mod*SN^4]], Expand[#]]& /@ mySystem;

    (* Returns the simplified system. *)
    Return[mySystem];

  ];


mSolve`ListFormation[eqnList0_, Form_, funcRules_, myTrackingVariableMax_]:=
  Block[{ mPowerListFormationDebug = False,
          eqnList = eqnList0,
          mList
         },

    eqnList = 
      ( Table[Coefficient[#, myTrackingVariable[i] ], 
          {i, 1, myTrackingVariableMax}
        ]& /@ eqnList0) /. 0:>Sequence[];

    If[mPowerListFormationDebug,
      Print["The system further divided, is: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Breaks up expressions into lists of terms. *)
    eqnList = 
      If[Head[#]===Plus, List @@ #, {#}]& /@ #& /@
        MapAll[Expand, eqnList];

    If[mPowerListFormationDebug,
      Print["The system where + -> {} is:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Pulls off the exponents of T and forms a list *)
    (* of expressions of the form {{{1+m[1]},{..}..}..}  *)
    mList = 
      Union[
        Exponent[#, 
          MapAll[Factor, Form] /. funcRules
        ]& /@ 
      #]& /@ eqnList;

    If[mPowerListFormationDebug,
      Print["The list of powers of F is:"];
      Print[CleanUpFunction[mList]];
    ];

   (* Returns the number of equations and the list of powers. *)
   Return[mList];
  ];


mSolve`Simplification[mList0_]:=
  Module[{mPowerListSimplificationDebug = False,
          mList, (* The list of powers. *)
          mListStructure (* Structure of powers. *)
         }, (* Protected Local Variables. *)

    (* The following lines breaks up the list of exponents *)
    (* of T and then removes invalid cases. *)

    (* Breaks up the expressions of $a+b \, m_i+c\, m_j+\dotsc$ *)
    (* where $a,b,c,\dotsc,i,j,k,\dotsc\in\mathbb{R}$ into lists. *)
    mList = 
      If[Head[#]===Plus, 
        List @@ #, 
        If[(Head[#]===m || Head[#]===n) || Head[#]===Times, 
          {#}, 
          #
        ]
      ]& /@ mList0;

    If[mPowerListSimplificationDebug,
      Print["Breaks up $a+b m_i+c m_j+\dotsc$ into lists:"];
      Print[CleanUpFunction[mList]];
    ];

    (* The following routine strips off the $a$ in the above *)
    (* expression and leaves only the underlying structure. *)
    mListStructure = Union[mList /. {a_Integer, b__}:>{b}];

    If[mPowerListSimplificationDebug,
      Print["The above sans $a$:"];
      Print[CleanUpFunction[mListStructure ]];
    ];

    (* Re-organizes the list of powers of T by the structure *)
    (* listed above. *)
    mList = 
      Cases[mList, {_, Sequence @@ #} | #]& /@ mListStructure;

    If[mPowerListSimplificationDebug,
      Print["The list of powers reorganized by structure:"];
      Print[CleanUpFunction[mList ]];
    ];

    (* Determines the maximum $a$ in each power of T *)
    mList = 
      {Max[# /. {a_, ___}:>If[IntegerQ[a], a, 0]& /@ #]}& /@ mList;

    If[mPowerListSimplificationDebug,
      Print["The list of powers after powers which cannot be "<>
            "the highest power are removed:"];
      Print[CleanUpFunction[mList ]];
    ];

    (* Creates a list of the maximum powers of T, such *)
    (* that all the members of the list are of the form *)
    (* $a_{\rm max}+b\,m_i+c\,m_j+\dotsb+d\,m_i\,m_j$ *)
    mList = 
      (Plus @@ Flatten[#])& /@ 
        Transpose[{mList, mListStructure}];

    If[mPowerListSimplificationDebug,
      Print["Formulates the powers back into the correct form:"];
      Print[CleanUpFunction[mList ]];
    ];

    (* Returns the simplified list. *)
    Return[mList];

 ];

mSolve`RulesSolver[mList0_, myMList_]:=
  Module[{rulesSolverDebug = False,
          mList,
          eqnList,
          mRules (* List of rules from first solve. *)
         }, (* Protected local variables. *)

    (* Makes sure it is the simplest list possible *)
    (* for combinatorial purposes. *)
    mList = Union[mSolve`Simplification[mList0] ];

    If[rulesSolverDebug,
      Print["The mList used in Power Solver is"];
      Print[CleanUpFunction[mList]];
    ];    

    (* Forms a list of equations to be solved for m_i. *)
    eqnList =   
      Flatten[
        Map[
          Thread[
            Table[#[[1]], {Length[#] -1} ] == Drop[#, 1]
          ]&,
          Table[Drop[mList, i], 
            {i, 0, Length[mList] - 2}
          ]
        ],
        1
      ];

    If[rulesSolverDebug,
      Print["The Equations to be solved first"];
      Print[CleanUpFunction[eqnList]];
    ];    

    (* Does the first run of solving. *)
    mRules = 
      Union[
        Flatten[
          Solve[#, myMList]& /@ eqnList
        ]
      ];

    If[rulesSolverDebug,
      Print["The first set of solutions are"];
      Print[CleanUpFunction[mRules]];
    ];    

    Return[mRules];
  ];

mSolve`PowerSolver[mRules0_, myMList_]:=
  Module[{powerSolverDebug = False,
          mRules = Sort[mRules0, (Length[#1] < Length[#2])&],
          numberOfEquations = Length[myMList]
         }, (* Protected local variables. *)

    If[powerSolverDebug,
      Print["The mRules used in Power Solver (sorted from " <>
            "shortest to longest) is:"];
      Print[CleanUpFunction[mRules]];
    ];    

    (* A little warning message if there is a combinatorial explosion. *)
    If[Binomial[Length[Flatten[ mRules ] ], numberOfEquations] > 100,
      CellPrint[
        Cell["Formulating and solving up to " <>
          ToString[ Binomial[Length[mRules], numberOfEquations] ] <>
          " systems of equations.  Please be patient.",
          "Message"
        ]
      ];
    ];

    (* Forms a list of equations to be solved for m_i. *)
    eqnList = 
      Outer[List, Sequence @@ (mRules /. Rule->Equal)];

    If[powerSolverDebug,
      Print["The next set of equations to be solved are:"];
      Print[CleanUpFunction[eqnList]];
    ];   

    (* Takes these solutions and uses them to find *)
    (* actual integer solutions to $m_i$ *)
    mSoln = 
      Union[
        Sequence @@ 
          ( Sequence @@ Solve[#, myMList]& /@ #
          )& /@ eqnList
      ];

    If[powerSolverDebug,
      Print["The solutions are:"];
      Print[CleanUpFunction[mSoln]];
    ];

   (* Returns the solutions *)
   Return[mSoln];
  ];

mSolve`SystemCleanUp[eqnList0_, mList_, mSoln0_, myMList_, F_]:=
  Module[{systemCleanUpDebug = False,
          mSoln = Union[Sort /@ mSoln0], 
          chiList = {},
          eqnList
         }, (* Protected local variables. *)

     (* Applies the solutions to the expressions of m_i. *)
     mSoln = 
      Transpose[{(mList //. #)& /@ mSoln, mSoln}];

     If[systemCleanUpDebug,
       Print["The expressions of m_i after possible " <>
             "solution substitution:"];
      Print[CleanUpFunction[mSoln]];
    ];

    mSoln = 
      mSoln /. 
        {a_List, {(_Rule)..}} :> Sequence[] /;
          Not[ And @@ (FreeQ[ a, #] & /@ myMList  ) ];

    If[systemCleanUpDebug,
      Print["mSoln, after the underdetermined systems are removed:"];
      Print[CleanUpFunction[mSoln]];
    ];

    (* _? NonPositive :> Sequence[] added by DB on 12/16/2002 *)
    mSoln = 
      mSoln /.
        { {a_List, b : {(_Rule) ..}} :> 
            b  /; And @@ ((Length[ Cases[#, Max[#]] /. _? NonPositive :> Sequence[] ] >= 2)& /@ a),
          {a_List, b : {(_Rule) ..}} :> 
            Sequence[]
        };

    If[systemCleanUpDebug,
      Print["mSoln, after power balances are checked:"];
      Print[CleanUpFunction[mSoln]];
    ];

    (* Removes Tracking Variables. *)
    eqnList = eqnList0 /. myTrackingVariable[_]:>1;

    If[systemCleanUpDebug,
      Print["eqnList, sans tracking variables is:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Forms chiList. *)
    eqnList /. \[Chi][i_] :> 
      ( chiList = Append[chiList, \[Chi][i] ]; 1 );
    chiList = Union[chiList];

    If[systemCleanUpDebug,
      Print["chiList, the list of \chi s are:"];
      Print[CleanUpFunction[chiList]];
    ];

    (* Finds constraints on \chi. *)
    eqnList = 
      MapAll[Factor,
        Plus @@ Coefficient[(eqnList /. #),
                  F^Max[mList /. mSoln]
                ]& /@ mSoln
      ];

    If[systemCleanUpDebug,
      Print["mSoln, Checking in eqnList:"];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Returns the good solutions. *)
    Return[mSoln];

  ];


(* Finds free solutions that result from inequalities. *)
(* Added direct from old code on 11/20/2002 by DB. *)
mSolve`FreeSolutions[mSoln_List, mList0_List]:=
  Module[{ mSoln0, (* Initial solutions *)
           mList = Flatten /@ mList0,
           checkList, (* dominate terms *)
           freeVariable, 
           freeVariableMax, 
           mSolnFree = {},
           freeDebug = False
         }, (* Local Variables *)

    (* Sets up a local variable with these solutions. *)
    mSoln0 = mSoln;

    If[freeDebug,
      Print["DB 11/20/2002 mSoln = "];
      Print[CleanUpFunction[mSoln]];
      Print["DB 11/20/2002 mList = "];
      Print[CleanUpFunction[mList]];
    ];

    (* Pulls off the polynomials in m_i which are the *)
    (* dominant terms. *)
    checkList =
      Table[
        DeleteCases[
          Union[
            Flatten[
              Table[
                Table[
                  If[
                    Evaluate[mList[[i,k]] /. mSoln[[j]] ] ==
                      Max[mList[[i]]/.mSoln[[j]]],
                    mList[[i,k]]
                  ],
                  {k, Length[mList[[i]] ]}
                ],
                {j, Length[mSoln]}
              ]
            ]
          ], 
          Null
        ], 
        {i,Length[mList]}
      ];

    If[freeDebug,
      Print["DB 11/20/2002 checkList = "];
      Print[CleanUpFunction[checkList]];
    ];

    (* Checks to see if any of the highest powers are *)
    (* based on a term which is based on only one m_i *)
    (* If this is the case, it may self balance. *)
    freeVariable = 
      DeleteCases[
        Flatten[
          Table[
            If[
              Length[
                Cases[checkList[[i]], 
                  ___Integer+__*m[j]|___Integer+m[j] 
                ] 
              ]>1 && 
              Length[mList]>1,
              m[j], 
              Null
            ],
            {j, Length[mList]},
            {i, Length[mList]}
          ]
        ], 
        Null
      ];

    If[freeDebug,
      Print["DB 11/20/2002 freeVariable = "];
      Print[CleanUpFunction[freeVariable ]];
    ];

    (* The following code runs only if an inequality *)
    (* exists and solutions might have been missed.   *)
    (* To find the missing solutions, it does a count- *)
    (* down scheme and then test them to see if any   *)
    (* of them are valid choices. *)
    If[Length[freeVariable]=!=0,
      freeVariableMax =   
        Max[
          Table[freeVariable[[j]] /. mSoln[[i]], 
            {i, Length[mSoln]},
            {j, Length[freeVariable]}
          ] 
        ];

      If[freeDebug,
        Print["DB 11/20/2002 freeVariableMax = "];
        Print[CleanUpFunction[freeVariableMax ]];
      ];

      mSolnFree =    
        Partition[
          Flatten[
            Fold[Table, 
              Table[m[i]->beta[i], {i, Length[mList]}], 
              Table[{beta[k],1,freeVariableMax},{k,Length[mList]}]
            ]
          ],
          Length[mList]
        ];

      If[freeDebug,
        Print["DB 11/20/2002 mSolnFree = "];
        Print[CleanUpFunction[mSolnFree ]];
      ];

      mSolnFree =   
        Complement[
          DeleteCases[
            Table[
              If[Plus @@ 
                Flatten[
                  Table[
                    If[
                      Length[
                        Cases[mList[[i]] /. mSolnFree[[j]], 
                          Max[mList[[i]] /. mSolnFree[[j]]] 
                        ]
                      ]>=2,
                      1, 
                      0
                    ], 
                    {i, Length[mList]}
                  ]
                ]>=Length[mList],
                mSolnFree[[j]], 
                Null
              ], 
              {j, Length[mSolnFree]}
            ], 
            Null
          ], 
          mSoln
        ]
      ];
    
    If[freeDebug,
      Print["DB 11/20/2002 mSolnFree = "];
      Print[CleanUpFunction[mSolnFree ]];
    ];

    (* Displays message to user if freedom exists. *)
    Do[
      If[
        Length[
          Cases[checkList[[i]], 
            ___Integer+__*m[j]|___Integer+m[j] 
          ] 
        ]>1 && 
        Length[mList]>1,
        Message[PDESpecialSolutionsmSolver::freedom, 
          CleanUpFunction[Cases[checkList[[i]],
            ___Integer+__*m[j]|___Integer+m[j] ]
          ], 
          i
        ] 
      ],
      {j, Length[mList]},
      {i, Length[mList]}
    ];

    If[freeDebug,
      Print["DB 11/20/2002 mSoln = "];
      Print[CleanUpFunction[Join[mSoln, mSolnFree]]];
    ];

    (* Return the solution *)
    Return[Join[mSoln, mSolnFree] ];
  ];


(* ************************************************************************ *)
(* : Title : PDESpecialSolutionsBuildSystem.
*  : Author : Douglas Baldwin
*  : Date : 05-24-01 *)
(* : Update : 1/12/2003 by Douglas Baldwin
*    Added debug statements and highest order equation solving.
*    Changes marked with DB:Date *)
(* : Update : 1-21-2003 by Douglas Baldwin
*    Added StripNonZero to the equations before they are sent to the solver.
*    This is mainly for printing the simplest system to the user, because 
*    AnalyzeAndSolve already strips the non-zeros. *)

PDESpecialSolutionsBuildSystem[mSoln_List, system_List, 
  vars_List, parameters_List, opts___?OptionQ]:=
  Block[{buildSystemDebug = False,
         Form,
         numberOfEquations,
         sqrtRules,
         funcRules,
         uRules,
         tempuRules,
         newSystem,
         waveparameters,
         param,
         unknowns,
         nonzeros,
         maxF,
         highestOrderSystem,
         highestOrderSolutions,
         myTemp,
         time = TimeUsed[]}, (* Protects Local Variables. *)

    (* Sets the form from the options. *)
    Form = 
      ToExpression[
        ToLowerCase[
          ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
        ]
      ] /. {jacobisn->sn, jacobicn->cn};

    (* Sets a local variable to the number of equations given by user. *)
    numberOfEquations = Length[system];

    (* Sets up the way in which the system will be divided up *)
    (* in the next step, based on the Options set by the user. *)
    sqrtRules = 
      {tanh -> 0, 
       sech -> 0, 
       sechtanh -> 1-S^2,
       cn -> 0,
       sn -> 0
      };

    (* Sets up a list of rules for replacing the form to F. *)
    funcRules = {tanh -> T, sech -> S, sechtanh -> S, cn -> CN, sn -> SN};

    (* Converts the results of mSolve to an expression in T *)
    uRules =  (# /.
      (m[i_]->j_) :>
        (u[i][Form /. funcRules] -> 
          Evaluate[Sum[a[i,kk]*(Form /. funcRules)^kk, {kk, 0, j}] + 
            If[(Form /. sqrtRules) =!= 0,
              Sqrt[Form /. sqrtRules]*
                Sum[b[i,kk]*(Form /. funcRules)^kk, 
                  {kk, 0, n[i] /. Flatten[#]}
              ],
              0
            ]
          ]
        )
       )& /@ mSoln;

    (* WILLY 12/19/2001 modification: introduced tempuRules *)
    If[Verbose /. {opts} /. Options[PDESpecialSolutions],
      Print["Seeking polynomial solutions of the form"];
       tempuRules = DeleteCases[uRules,
            n[_]->_,
            2];
      Print[
        CleanUpFunction[
          DeleteCases[tempuRules,
            max[_]->_,
            2
          ]
        ]
      ]
    ];

    (* Prints out a warning, if it's taking a long time. *)
    If[TimeUsed[]-time>3,
      Print["Still building the nonlinear algebraic system, please wait."]
    ];

    (* Converts form of solutions given by solver to a pure *)
    (* function. *)
    toPure = 
      (# /. (a__[var__]->temp__):> (a:>Function[{var}, temp]))&;

    (* Applies the expressions in T to the system and removes the *)
    (* tracking variables. *)
    newSystem = 
      Expand[
        system //. Append[toPure[#], myTrackingVariable[_]->1]
      ]& /@ uRules;

    If[buildSystemDebug,
      Print["Apply the expressions in T to the sytem gives: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Clears the denominator to simplify the system. *)
    newSystem = 
      Map[Together[#*Denominator[Together[#]]]&, newSystem, 2];

    If[buildSystemDebug,
      Print["Clearing the denominator, we get: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Creates a list with the wave parameters (c[1], c[2], ...) to be *)
    (* passed to the solver. DB:2-4-2003 Put mod with param instead of c_is.*)
    waveparameters = 
        Table[c[i], {i, Length[vars]}];

    (* DB:2-4-2003 Including mod with parameters. *)
    param = 
      Join[parameters,
        If[Form === cn || Form === sn, {mod}, {}]
      ];


    (* Creates a list of all the a[i,j]'s to be passed to the solver. *)
    unknowns =
      Table[
        {Table[a[i,j], {j, 0, m[i] /. #}],
          If[(n[i] /. # /. n[_]->0) > 0,
            Table[b[i,j], {j, 0, n[i] /. # /. n[_]->0}],
            Null
          ]}, 
        {i, numberOfEquations}]& /@ mSoln;

    unknowns = 
      DeleteCases[Sequence @@ #& /@ #& /@ unknowns, Null, Infinity];

    (* Creates a list of those variables which must be nonzero, so as *)
    (* to simplify the work of the solver. *)
    (* DB:1/12/2003 Commented out the Form =!= cn and sn. *)
    nonzeros = 
      Join[param, 
        If[Form =!= sechtanh (* && Form =!= cn && Form =!= sn *), Last /@ #, {}], 
        waveparameters
      ]& /@ unknowns;

    (* Flattens the sublists and reorders them to speed up the solver. *)
    unknowns = 
    Map[
        Reverse,
           #[[2]]& /@ #& /@ 
           (Sort[{# /. a_[b_,c_]:>{c,a,b},#}& /@ Flatten[#] ]& /@ unknowns) 
       ];

    If[buildSystemDebug,
      Print["The unknowns, nonzeros and wave parameters are: "];
      Print[CleanUpFunction[{unknowns, nonzeros, waveparameters} ]];
    ];

    (* Expands the system. *)
    newSystem = MapAll[Expand,newSystem];

    (* Determines the maximum value of F in each of the cases. *)
    maxF = 
      Map[
        Exponent[#, 
          Form /. funcRules
        ]&, 
        newSystem
      ];

    If[buildSystemDebug,
      Print["The dominate power in each expression of new system is: "];
      Print[CleanUpFunction[ maxF ]];
    ];

    (* UnsortedUnion from Mathematica Book -- added by DB on 1/11/2003. *)
    (* Removed on Tuesday, January 14, 2003 by DB 
    UnsortedUnion[x_] := Module[{f}, f[y_] := (f[y] = Sequence[]; y); f /@ x];
    *)

    (* If the HigestOrderFirst option is set, then: *)
    If[HighestOrderFirst /. {opts} /. Options[PDESpecialSolutions],
      (* Creates a list of the highest order system.  Rewritten by DB:1/14/2003 *)
      highestOrderSystem = 
        (# == 0)& /@ 
          MapThread[Coefficient[#1, Form /. funcRules, #2] &, 
            {#, Exponent[#, Form /. funcRules]}]& /@ newSystem;
      
      If[buildSystemDebug,
        Print["The highest order equations are: "];
        Print[CleanUpFunction[ highestOrderSystem ]];
      ];

      (* DB:1-21-2003, Strips the non-zeros at this step. *)
      highestOrderSystem = MapThread[StripNonZero, {highestOrderSystem, nonzeros} ];

      If[buildSystemDebug,
        Print["Removes non-zeros from the system."];
        Print[CleanUpFunction[ highestOrderSystem ]];
      ];

      (* DB:1/12/2003 highestOrderSytem is then formated to *)
      (* input into AnalyzeAndSolve *)
      highestOrderSystem = 
        MapAll[Factor,
          Transpose[
            {highestOrderSystem, 
              unknowns, 
              Table[waveparameters, {Length[newSystem]}],
              Table[param, {Length[newSystem]}],
              nonzeros
            }
          ]
        ];

      If[buildSystemDebug,
        Print["The highest order system formated for AnalyzeAndSolve: "];
        Print[CleanUpFunction[ highestOrderSystem ]];
      ];

      (* DB:1/12/2003 Find the solutions using AnalyzeAndSolve *)
      highestOrderSolutions = 
        Algebra`AnalyzeAndSolve`AnalyzeAndSolve @@ #& /@ 
          highestOrderSystem;

      If[buildSystemDebug,
        Print["The highest order equations' solutions are: "];
        Print[CleanUpFunction[ highestOrderSolutions ]];
      ];
    ];


    (* Sets up the way in which the system will be divided up *)
    (* in the next step, based on the Options set by the user. *)
    sqrtRules = 
      {tanh -> Null, 
       sech -> 1-S^2, 
       sechtanh -> 1-S^2,
       cn -> 1-mod-CN^2+2*mod*CN^2-mod*CN^4, 
       sn -> 1-SN^2-mod*SN^2+mod*SN^4
      };

    (* Breaks up system into most general form. *)
    newSystem = 
      Flatten[
       {Coefficient[#,Sqrt[Form /. sqrtRules],0]& /@ #, 
        Coefficient[#,Sqrt[Form /. sqrtRules],1]& /@ #}
      ]& /@ #& /@ newSystem;

    If[buildSystemDebug,
      Print["After breaking the system up into {P,Q} (where P + Sqrt[]*Q): "];
      Print[CleanUpFunction[ newSystem ]];
    ];
    
    (* Brakes the expressions up newSystem by powers of T. *)
    (* Modified version by DB:1/11/2003 *)
    newSystem = 
      Table[
        Table[
          Union[
              DeleteCases[
                Flatten[
                  Table[
                    Table[
                      Coefficient[
                        Expand[newSystem[[case,k]] ], 
                        Form /. funcRules, 
                        i
                      ], 
                      {i, 0, maxF[[case,j]]}], 
                    {j, Length[maxF[[case]] ]}
                  ]
                ], 0
              ]
          ], {k, Length[newSystem[[case]] ]}
        ], {case, Length[newSystem]}
      ];

    If[buildSystemDebug,
      Print["The system after being broken up is: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Converts from expressions to equations. *)
    newSystem = 
      DeleteCases[(# == 0)& /@ Flatten[#]& /@ newSystem,
        False || True, Infinity];

    If[buildSystemDebug,
      Print["After flattening and removing True/Falses:"];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* DB:1-21-2003, Strips the non-zeros at this step. *)
    newSystem = 
      MapThread[StripNonZero, {newSystem, nonzeros} ];

    If[buildSystemDebug,
      Print["Removes non-zeros from the system."];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Prints out a warning if it's taking too long. *)
    If[
   (TimeUsed[]-time>3) && !(Verbose /. {opts} /. Options[PDESpecialSolutions]),
      Print["Still building the nonlinear algebraic system, please wait."]
    ];

    If[HighestOrderFirst /. {opts} /. Options[PDESpecialSolutions],
      (* DB:11/13/2002 Version to work with highest order solutions *)
      (* Combines into lists containing {newSystem, unknowns, *)
      (* waveparameters, param, nonzeros} for the solver. *)
      Return[
       MapAll[Factor, 
         (* Expands the cases over the solutions for the highest terms *)
         (Sequence @@ 
            ( { (* Added Flattens on 11/13/02 to compensate *)
                (* for the output of highestOrderSolutions  *)
                (* StripNonZero added on 2/2/2003 by DB. *)
               StripNonZero[
                 Flatten[(First[#] /. Last[#]) /. True -> Sequence[] ],
                 #[[-2]]
               ], 
               Sequence @@ Drop[Rest[#],-1],
               Flatten[Last[#]]
              }& /@ Thread[#, List, -1]
            )
         ) & /@ 
       (* Groups the information in the same form as the input to the solver. *)
           Transpose[
            {newSystem, 
              unknowns, 
              Table[waveparameters, {Length[newSystem]}],
              Table[param, {Length[newSystem]}],
              nonzeros,
              highestOrderSolutions
            }
          ]
       ]
      ],
      (* Combines into lists containing {newSystem, unknowns, *)
      (* waveparameters, param, nonzeros} for the solver. *)
      Return[
        MapAll[Factor, 
          Transpose[
            {newSystem, 
              unknowns, 
              Table[waveparameters, {Length[newSystem]}],
              Table[param, {Length[newSystem]}],
              nonzeros
            }
          ]
        ]
      ]
    ];

  ];

(* ************************************************************************ *)

(* : Title : PDESpecialSolutionsBuildSolutions. *)
(* : Author : Douglas Baldwin *)
(* : Summary : Builds (includes massive simplification) *)
(*   and test the final solutions. *)

PDESpecialSolutionsBuildSolutions[solution_, mSoln_, eqns_, funcs_, vars_, 
  param_, opts___?OptionQ] :=
  Block[{Form, (* Form defined by user. *)
         solutionRules, (* Local version of solution *)
         sqrtRules, (* Set by options. *)
         funcRules, (* Also set by options. *)
         uRules, (* Rules for creating the solutions. *)
         mySimplificationRules, (* Simplification rules *)
         numericTestSolutions, (* tests validity of solutions *)
         symbolicTestSolutions, (* Also, tests the validity of soln. *)
         solns = {}, (* confirmed solutions. *)
         warn = {}, (* Collects a list of warnings due to simplification. *)
         time = TimeUsed[] (* A timer for length warnings. *)
        }, (* Protected Local Variables. *)

    (* Sets the form from the options. *)
    Form = 
      ToExpression[
        ToLowerCase[
          ToString[Form /. {opts} /. Options[PDESpecialSolutions]]
        ]
      ] /. {jacobisn -> sn, jacobicn -> cn};

    (* Sets up a local version to modify *)
    solutionRules = MapAll[Factor, solution]; 

    (* Rules for building the solutions. *)
    sqrtRules = 
      {tanh -> 0, 
       sech -> 0, 
       sechtanh -> 
         1-Sech[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}] + phase]^2,
       cn -> 0,
       sn -> 0
      };
    funcRules = 
      {tanh -> 
         Tanh[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase], 
       sech -> 
         Sech[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase], 
       sechtanh -> 
         Sech[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase],
       cn -> 
         CN[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase,mod],
       sn -> 
         SN[Plus @@ Table[c[i]*vars[[i]], {i, Length[vars]}]+phase,mod]
      };

    (* Converts the results of mSolve to an expression in T *)
    uRules =  
      (m[i_]->j_) :>
        (funcs[[i]] -> 
            Sum[a[i,kk]*(Form /. funcRules)^kk, {kk, 0, j}] + 
            Sqrt[Form /. sqrtRules]*
              Sum[b[i,kk]*(Form /. funcRules)^kk, 
                {kk, 0, n[i] /. Flatten[#]}
              ] 
        )&;

    (* Builds the solutions from the above rules and *)
    (* the powers of F listed in the passed mSoln. *)
    solutionRules = DeleteCases[DeleteCases[
      DeleteCases[
        Table[
          Table[
            Join[(mSoln[[jj]] /. uRules[mSoln[[jj]] ]) //. 
                solutionRules[[jj, ii]],
              (# -> (# /. solutionRules[[jj,ii]]))& /@
              If[Form === cn || Form === sn, 
                Append[param, mod], 
                param
              ]
            ],
            {ii, Length[solutionRules[[jj]]]}],
        {jj, Length[mSoln]}],
        max[_]->_,
        Infinity
      ],
      n[_]->_,
      Infinity],
    Rule[a_, b_] /; a == b && FreeQ[a, Alternatives @@ funcs],
    Infinity];

    (* Simplification rules for reducing the solution *)
    (* even further . . . so as to find more general  *)
    (* solutions. *)
    mySimplificationRules = 
      { Sqrt[xxx__^2] :> 
          (warn = Append[warn, "Sqrt[a^2]->a"]; xxx), 
        Sqrt[Power[yyy__,2]] :> 
          (warn = Append[warn, "Sqrt[a^2]->a"]; yyy), 
        Sqrt[-zzz__^2] :> 
          (warn = Append[warn, "Sqrt[-a^2]->I*a"]; I*zzz),
        Sqrt[-ttt_*zzz__^2] :> 
          (warn = Append[warn, "Sqrt[-a*b^2]->I*b*Sqrt[a]"];
           I*zzz*Sqrt[ttt]), 
        (1-Sech[xx__]^2) -> Tanh[xx]^2,
        (1-Tanh[xx__]^2) -> Sech[xx]^2,
        JacobiDN[xx__, mm__]^2 :> 1-mm+mm*JacobiCN[xx,mm]^2 /; Form === cn,
        JacobiSN[xx__, mm__]^2 :> 1-JacobiCN[xx,mm]^2 /; Form === cn,
        JacobiDN[xx__, mm__] :> 
     (warn = Append[warn,"JacobiDN[x,mod]->Sqrt[1-mod+mod*JacobiCN[x,mod]^2]"];
           Sqrt[1-mm+mm*JacobiCN[xx,mm]^2]
          ) /; Form === cn,
        JacobiSN[xx__, mm__] :> 
          (warn = Append[warn,"JacobiSN[x,mod]->Sqrt[1-JacobiCN[x,mod]^2]"];
           Sqrt[1-JacobiCN[xx,mm]^2]
          ) /; Form === cn,
        JacobiDN[xx__, mm__]^2 :>1-mm*JacobiSN[xx,mm]^2 /; Form === sn,
        JacobiCN[xx__, mm__]^2 :> 1-JacobiSN[xx,mm]^2 /; Form === sn,
        JacobiDN[xx__, mm__] :> 
          (warn = Append[warn,
                    "JacobiDN[x,mod]->Sqrt[1-mod*JacobiSN[x,mod]^2]"
                  ];
           Sqrt[1-mm*JacobiSN[xx,mm]^2]
          ) /; Form === sn,
        JacobiCN[xx__, mm__] :> 
          (warn = Append[warn, 
                    "JacobiSN[x,mod]->Sqrt[1-JacobiSN[x,mod]^2]]"
                  ];
           Sqrt[1-JacobiSN[xx,mm]^2]
          ) /; Form === sn
      };
 
    (* Applies the above rules to the solutions. *)
    solutionRules = 
      FixedPoint[
        MapAll[Expand,
          MapAll[Factor, 
            # //. mySimplificationRules
          ] //. mySimplificationRules
        ]&,
        solutionRules,
        3
      ];

    (* Removes Trivial Solutions *)
    solutionRules =
      Select[#, 
        !(And @@ (FreeQ[# /. (a_->b__):>b, Alternatives @@ vars]& /@ #))&
      ]& /@ solutionRules;

    If[Verbose /. {opts} /. Options[PDESpecialSolutionsr],
      Print["The possible non-trivial solutions (before any testing) are: "];
      Print[
   CleanUpFunction[solutionRules /. {CN -> JacobiCN, SN -> JacobiSN}
        ]]
      ];

    (* Prints out a warning, if it's taking a long time. *)
    If[TimeUsed[]-time>3,
      Print["Still building the exact solutions, please wait."]
    ];

    (* Depending on the NumericTest option, it either tests the *)
    (* solutions numerically, or it doesn't. *)
    If[ ( !(NumericTest /. {opts} /. Options[PDESpecialSolutions]) &&
          !(SymbolicTest /. {opts} /. Options[PDESpecialSolutions]) ),
      CellPrint[
        Cell[
        "These solutions are not being tested numerically or symbolically. " <>
        "To test the solutions set either the NumericTest option " <>
        "to True, or set the SymbolicTest option to True, or both. ", 
        "Message"
        ]
      ];
      If[Length[warn]>0,
        CellPrint[
          Cell[
          "The following simplification rules are being used: " <>
          ToString[Union[warn]],
          "Message"
          ] 
        ]
      ];
      Return[
        Map[Union,
          MapAll[Factor,
            MapAll[Expand,
              solutionRules /. {CN -> JacobiCN, SN -> JacobiSN}
            ]
          ], 2
        ]
      ]
    ];

    (* Converts form of solutions given by solver to a pure function. *)
    toPure = 
      (# /. (a__[var__]->temp__):> (a:>Function[{var}, temp]))&;

    (* If statement for the numeric testing option. *)
    If[NumericTest /. {opts} /. Options[PDESpecialSolutions],
      (* Sends message to user. *)
      If[!(VerboseTest /. {opts} /. Options[DDESolve]),
        Print["Numerically testing the solutions."]
      ];

      (* Tests numerically to make sure the above solutions are valid. *)
      numericalTestSolutions =
        {(eqns /. a__==b__:>a-b) /. toPure[MapAll[TrigToExp, #]], #}& /@ 
          #& /@ solutionRules;

      (* Numerically tests the solutions by replacing all the symbols with *)
      (* random numbers 13 separate times. *)
      numericalTestSolutions = 
       {Plus @@ 
        (Table[
           (* Prints out a warning, if it's taking a very long time. *)
           If[TimeUsed[]-time>3,
             time = TimeUsed[]+1;
             Print["Still numerically testing the solutions, please wait."]
           ];
           And @@
             (
               (
                 Abs[# /.
                   {a[_,_]->Random[], (* coefficients in polynomial *)
                    b[_,_]->Random[], (* coefficients in polynomial *)
                    Sequence @@ ((# -> Random[])& /@ 
                        If[Form === cn || Form === sn, 
                          Join[param, {mod}], 
                          param
                        ] 
                      )
                   } /. 
                   {CN -> JacobiCN, SN-> JacobiSN}] < 10^(-10) 
               )& /@
               MapAll[ Expand,
                 #[[1]] /. 
                   (Append[
                    (# -> Random[])& /@ 
                      Join[vars, Array[c, Length[vars]]],
                    phase -> 0
                    ]
                   )
               ]
             ),
             {13}
          ] /. {True->1, False->0}
        ),
        #
       }& /@ #& /@ numericalTestSolutions;

      (* If it works for any of the 13 times, it keeps the solution. *)
      (* This works out to be about a 0.0001 chance of missing *)
      (* a correct solution *)
      solns = 
        Cases[numericalTestSolutions,
          {a_Integer/;a>0, _List},
          Infinity
        ] //. {_Integer, a_List}:>{a[[2]]};
    ];

    (* The second testing If statement. *)
    If[SymbolicTest /. {opts} /. Options[PDESpecialSolutions],
      (* Sends message to user. *)
      If[!(VerboseTest /. {opts} /. Options[DDESolve]),
        Print["Symbolically testing the solutions."]
      ];

      (* This sets up the input for the next block of code. *)
      (* In that, it takes the question given by the user, *)
      (* and replaces the user defined functions (e.g. u[x,t]) *)
      (* with the functions found with the algorithm.  To replace *)
      (* the partial derivatives correctly, we must first convert *)
      (* the solutions to pure functions. *)
      symbolicTestSolutions =
        {(eqns /. a__==b__:>a-b) /. toPure[MapAll[TrigToExp, #]], #}& /@ 
          #& /@ (solutionRules /. {CN -> JacobiCN, SN-> JacobiSN});

      (* Attempts to simplify the expressions as much as possible. *)
      symbolicTestSolutions = 
        ExpToTrig[
          FixedPoint[ 
            MapAll[Factor, 
              MapAll[Expand, #] /. mySimplificationRules
            ] /. mySimplificationRules &, #, 10]&
            /@ symbolicTestSolutions
        ];

      (* Pulls of the solutions which simplify to zero, and adds *)
      (* them to solns (the final output applies the union, so *)
      (* duplicate solutions are not an issue at this point). *)
      solns = 
        Join[solns,
          Cases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List}:>{a}
        ];

      (* Removes all the good cases, so we may output the bad *)
      (* ones to the user. *)
      symbolicTestSolutions = 
        DeleteCases[
          DeleteCases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ],
          {}
        ];

      If[(Map[Union, symbolicTestSolutions,3] //. {{}}->{}) != {},  
        (* Sends out the left over (questionable) solutions to *)
        (* the user for hand inspection. *)
        CellPrint[
          Cell[
          "These solutions did not simplify to zero.  " <>
          "Please test these equations by hand or interactively "<>
          "with Mathematica.",
          "Message"
          ]
        ];
        Print[CleanUpFunction[#]]& 
          /@ symbolicTestSolutions;
      ];
    ]; 

    If[Length[warn]>0,
      CellPrint[
        Cell[
        "The following simplification rules are being used " <>
        "to test the solutions: " <>
        ToString[Union[warn]],
        "Message"
        ]
      ]
    ];

    (* Returns the solution rules *)
    Return[
      Union[
        MapAll[Factor,
          MapAll[Expand,
            solns /. {CN -> JacobiCN, SN-> JacobiSN}
          ]
        ]
      ]
    ];
];

(* ************************************************************************ *)

(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "PDESpecialSolutionsPrivate`" from output. *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      "Calculus`PDESpecialSolutions`Private`"->""
    ]
  ]&


(* ************************************************************************ *)

(* : Title : StripNonZero *)
(* : Author : Douglas Baldwin *)
(* : Summary : Strips parameters from expressions. *)

StripNonZero[{a : (_List) ..}, param_List] := 
  StripNonZero[#, param] & /@ {a};

StripNonZero[theList_List, param_List] :=
    Module[
      {result, stripDebug = False}, (* Local Variables *)
     
      If[stripDebug,
        Print["The origional expression is: "];
        Print[CleanUpFunction[ MapAll[Factor, theList] ]];
      ];

      (* Maps factor to every term, so as to have a constant base. *)
      result =  FactorList /@ (theList /. Equal[a_,b_]:>a-b);
      
      If[stripDebug,
        Print["The results of FactorList is: "];
        Print[CleanUpFunction[ result ]];
      ];
      
      If[stripDebug,
        Print["The rules are: "];
        Print[CleanUpFunction[ {({#^_:1, _} :> Sequence[] & /@ param), {_?NumericQ, _} :> Sequence[]} ]];
      ];

      (* Remove terms that are non-zero. *)
      result = result /. ({#^_:1, _} :> Sequence[] & /@ param);

      (* Remove terms that are numeric. *)
      result = result /. {_?NumericQ, _} :> Sequence[];

      If[stripDebug,
        Print["The result after apply the non-zero rules: "];
        Print[CleanUpFunction[ result ]];
      ];
      
      (* Puts it back into standard form, {a, b} to a*b *)
      result = Times @@ (First[#]^Last[#]&) /@ #& /@ result;

      If[stripDebug,
        Print["Converting back to the standard form: "];
        Print[CleanUpFunction[ result ]];
      ];

      (* Converts expressions back into equations. *)
      If[! FreeQ[theList, Equal],
        result = Equal[#,0]& /@ result;
        ];

      If[stripDebug,
        Print["The final result of stripping the non-zeros is: "];
        Print[CleanUpFunction[ result ]];
      ];

      Return[ result ];
      ];

End[] (* `Private` context *)

Protect[PDESpecialSolutions]

SetAttributes[PDESpecialSolutions, ReadProtected]

EndPackage[]

(* ************************************************************************ *)

(* Nonlinear algebraic solver by Unal Goktas (WRI) and Willy Hereman *)
(* written by Unal Goktas in October/November 2000 *)
(* Comments added by Douglas Baldwin on Monday, January 13, 2003 *)
(* Reverted back to Non-HighestOrder code DB:2/2/2003 *)

BeginPackage["Algebra`AnalyzeAndSolve`"]

Unprotect[AnalyzeAndSolve]

Begin["`Private`"]

If[$VersionNumber < 4,
   Attributes[Internal`DeactivateMessages] = {HoldAll};
   Internal`DeactivateMessages[body_, msgs___MessageName] :=
      Module[{wasOn = Select[Hold[msgs], Head[#] =!= $Off &], result},
         CheckAbort[
            Scan[Off, wasOn];
            result = body;
            Scan[On, wasOn];
            result,
            Scan[On, wasOn];
            Abort[]
         ]
      ]
]

(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "Algebra`AnalyzeAndSolve`Private`" from output. *)
(* : Added for debugging for AnalyzeAndSolve by DB:1/14/2003 *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      { "Calculus`PDESpecialSolutions`Private`"->"",
        "Algebra`AnalyzeAndSolve`Private`"->""}
    ]
  ]&

(* This is the first call of AnalyzeAndSolve.  In this call, *)
(* The equations are converted into expressions equal to zero. *)
(* It also sets the default type of givensol to an empty list if *)
(* it is not present. *)
AnalyzeAndSolve[system: {HoldPattern[_ == _]..}, primaryunknowns_,
   secondaryunknowns_, parameters_, nonzeros_] :=
   AnalyzeAndSolve[(#[[1]]-#[[2]]&) /@ system, primaryunknowns,
      secondaryunknowns, parameters, nonzeros]

(* This case is called only if there are no parameters.  *)
(* In the case with no parameters, it is assumed that Mathematica's *)
(* Solve will be able to find a solution to the system of equations. *)
AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_,{},nonzeros_]:=
   Block[{constraints},
      constraints = (And @@ ((# != 0 &) /@ nonzeros));
      Internal`DeactivateMessages[
         Solve[(And @@ ((# == 0 &) /@ system)) && constraints,
            Join[primaryunknowns, secondaryunknowns], Sort -> False],
         Solve::svars
      ]
   ]

(* ************************************************************************ *)

(* Takes the newly recast version of AnalyzeAndSolve and converts its inputs *)
(* into a form readable by RecursivelyKeepTrack. *)
(* Warning: It is assumed that "system" is polynomial in "primaryunknowns", *)
(* "secondaryunknowns", and "parameters". *)
AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, parameters_,
   nonzeros_] :=
   Block[{a, globalsol = {}, constraints},
      a = Together[({#}& /@ system) /. {{}}];
      constraints = (And @@ ((# != 0 &) /@ nonzeros));
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, constraints]&, {a, {{}}}];
      Union[globalsol]
   ]

(* ************************************************************************ *)

(* Collects all the solutions at the end into globalsol. *)
(* Origional code . . . replaced by the two following functions. *)
RecursivelyKeepTrack[{}, sol_, __] := (AppendTo[globalsol, sol]; {})

(* Terminates that recursive branch if the solution expodes or indeterminate. *)
RecursivelyKeepTrack[system_, sol_, __] /;
   (!FreeQ[system, DirectedInfinity] || !FreeQ[system, Indeterminate]) := {}


(* Main RecursivelyKeepTrack call.  It takes the system, cleans it up, *)
(* sorts it by complexity level (heuristic based on the degree of the *)
(* polynomial and size of the expression), takes first equation solves *)
(* it, simplifies the solution and recursively calls it self on each *)
(* unique branch of the solution. *)
RecursivelyKeepTrack[system_, sol_, primaryunknowns_, secondaryunknowns_,
   parameters_, nonzeros_, constraints_] :=
   Block[{a, b, c, recursiveDebug = True},
      (* Breaks the expression into a list and removes nonzeros and numbers. *)
      a = FactorListAndCleanUp[#, primaryunknowns, secondaryunknowns,
             parameters, nonzeros]& /@ system;
      (* Removes duplicates. *)
      a = Union[a];
      (* Sorts the system by the "ComplexityLevel" heuristic which is the *)
      (* degree of the polynomial*100 + LeafCount size of the expression. *)
      a = Sort[a, (ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                      parameters] <=
                   ComplexityLevel[#2, primaryunknowns, secondaryunknowns,
                      parameters]&)];
      (* DB:1/14/2003 Print statement added for debugging. *)
      If[recursiveDebug,
        Print["The order of the equations in AnalyzeAndSolve is: "];
        Print[
          CleanUpFunction[
            {ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                        parameters],#1}& /@ a
          ]
        ];
      ];
      (* Takes the first equation of the system of equations (which is  *)
      (* the simplest according to the complexity heuristic) *)
      b = a[[1]];
      (* Then solves the first equation for only one variable. *)
      b = SolveStepByStep[#, primaryunknowns, secondaryunknowns, parameters,
                          constraints, sol]& /@ b;
      (* Flattens from the inside out:  {{{a,b},{c,d}}} -> {{a,b},{c,d}}. *)
      b = (Sequence @@ # &) /@ b;
      (* DB:2/4/2003 Added expand. *)
      b = MapAll[Expand, b];
      If[recursiveDebug,
        Print["The solution from the first equation is:"];
        Print[CleanUpFunction[ b ]];
      ];
      (* If there is no solution for the `simplest' equation, it terminates *)
      (* this recursive branch. *)
      If[Length[b] == 0, Return[{}]];
      (* Transposes the solution: {{a,b},{c,d}} -> {{a,c}, {b,d}} . *)
      b = Transpose[b];
      (* Adds constraints to the list, if there are any. .. && b && d *)
      c = (constraints && (And @@ #))& /@ b[[2]];
      (* Drops constraints. *)
      b = b[[1]];
      (* Applies the solution to the rest of the system and simplifies via *)
      (* a together and a numerator. *)
      a = Together[
             Internal`DeactivateMessages[Rest[a] /. b,
                Power::infy, General::indet
             ]
          ];
      a = Numerator[a];
      (* Removes any cases which it eliminates one of the other equations. *)
      a = DeleteCases[a, {___, 0, ___}, {2}];
      (* Takes the new solution, the one equation shorter system and the *)
      (* constraint and continues the recursive process. *)
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, #3]&, {a, b, c}]
   ]

(* ************************************************************************ *)

(* Performs a factor list and then removes from it any nonzeros or numbers. *)
(* Ex: -4 + 8a - 4b + 8ab - b^2 + 2ab^2 *)
(*    -> {{1, 1}, {-1 + 2*a, 1}, {2 + b, 2}} *)
(*     -> {{-1 + 2*a}, {2 + b}} *)
FactorListAndCleanUp[
   system_, primaryunknowns_, secondaryunknowns_, parameters_, nonzeros_] :=
   Block[{a = FactorList /@ system},
      (* DB:2/4/2003 Remove terms that are non-zero. *)
      a = a /. ({#^_:1, _} :> Sequence[] & /@ nonzeros);
      (* DB:2/4/2003 Remove terms that are numeric. *)
      a = a /. {_?NumericQ, _} :> Sequence[];
      a = Flatten[Map[First[#]&, a, {2}]];
      Union[a]
   ]


(* ************************************************************************ *)

(* New complexity analyzer by Douglas Baldwin on DB:2/3/2003 *)
ComplexityLevel[expr_List, primaryunknowns_, secondaryunknowns_, parameters_]:=
  Max[
    ComplexityLevel[#,primaryunknowns,secondaryunknowns,parameters] & /@ expr
  ]

ComplexityLevel[expr_,primaryUnknowns_,secondaryUnknowns_,parameters_]:=
  Module[
    { primaryComplexity = Select[primaryUnknowns, !FreeQ[expr,#]&],
      secondaryComplexity= Select[secondaryUnknowns, !FreeQ[expr,#]&],
      parameterComplexity= Select[parameters, !FreeQ[expr,#]&],
      exprLength = If[Head[expr] === Plus, Length[expr], 1],
      complexityDebug
     },
    
    primaryComplexity  = Exponent[expr, primaryComplexity] ; 
    secondaryComplexity= Exponent[expr, secondaryComplexity];
    parameterComplexity= Exponent[expr, parameterComplexity];
    If[complexityDebug,
      Print["The precept sequence for the complexity analyzer is: "];
      Print[
        CleanUpFunction[{primaryComplexity, secondaryComplexity, 
           parameterComplexity, exprLength}
        ]
      ];
    ];
    Return[
      Min @@ 
       Flatten[{1*primaryComplexity, 2*secondaryComplexity, 
         3*parameterComplexity}] + exprLength
    ];
  ];

(* ************************************************************************ *)

(* If there is more than one term in the expression (since it was converted *)
(* into a list of factors), it takes the maximum complexity of all the members *)
(* as the complexity. *)
(* Removed by DB:2/3/2003
ComplexityLevel[expr_List, primaryunknowns_,secondaryunknowns_,parameters_]:=
   Max[ComplexityLevel[#, primaryunknowns, secondaryunknowns, parameters]& /@
      expr]
*)

(* ************************************************************************ *)

(* This takes the expressions which contain primaryunknowns by formating *)
(* into a form readable by SubComplexity. a[1,2], a[2,1], ... *)
(* Removed by DB:2/3/2003
ComplexityLevel[expr_, primaryunknowns_, secondaryunknowns_, parameters_] :=
   Block[{a, b},
      a = Union[Cases[{expr}, q_ /; MemberQ[primaryunknowns, q], -1]];
      b = Length[a];
      (
       SubComplexityLevel[expr, a, b, 1]
      ) /; b != 0
   ]
*)

(* ************************************************************************ *)

(* This takes the expressions which contain secondaryunknowns by formating *)
(* into a form readable by SubComplexity. c[1], c[2], ... *)
(* Removed by DB:2/3/2003
ComplexityLevel[expr_, primaryunknowns_, secondaryunknowns_, parameters_] :=
   Block[{a, b},
      a = Union[Cases[{expr}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      b = Length[a];
      (
       SubComplexityLevel[expr, a, b, 2] 
      ) /; b != 0
   ]
*)

(* ************************************************************************ *)

(* This takes the expressions which contain parameters by formating *)
(* into a form readable by SubComplexity. alpha, beta, ... *)
(* Removed by DB:2/3/2003
ComplexityLevel[expr_, primaryunknowns_, secondaryunknowns_, parameters_] :=
   Block[{a, b},
      a = Union[Cases[{expr}, q_ /; MemberQ[parameters, q], -1]];
      b = Length[a];
      (
       SubComplexityLevel[expr, a, b, 3] 
      ) /; b != 0
   ]
*)

(* ************************************************************************ *)

(* This computes the leafs of the complexity analysis tree. *)
(* The complexity heuristic (smaller is better) is either *)
(*   a) the exponent of the expression if it is polynomial, or *)
(*   b) 100*b*level + size of expression, where b is the number *)
(*      of expressions which are of the level type (primary, secondary, *)
(*      parameter), and the level: primary = 1, secondary = 2, param = 3 *)
(* Removed by DB:2/3/2003
SubComplexityLevel[expr_, a_, b_, level_] :=
   Block[{c = Select[a, PolynomialQ[expr, #]&]},
      Which[
         Length[c] == 0,
         100*b*level+LeafCount[expr],
         True,
         Min[Exponent[expr, c]]
      ]
   ]
*)

(* ************************************************************************ *)

(* solves a single equation *)

(* Takes the factor terms which have the primary unknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with the secondary *)
(* unknowns, parameters, constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[primaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, 
          Flatten[{secondaryunknowns, parameters}],
          constraints, sol
       ]
      ) /; Length[a] != 0
   ]

(* ************************************************************************ *)

(* Takes the factor terms which have the secondaryunknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with parameters,  *)
(* constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, parameters, constraints, sol]
      ) /; Length[a] != 0
   ]

(* ************************************************************************ *)

(* Takes the factor terms which have the paramaters and pass it on to the *)
(* SubSolveStepByStep to be solved along with cosntraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[parameters, q], -1]];
      (
       SubSolveStepByStep[eqn, a, {}, constraints, sol]
      ) /; Length[a] != 0
   ]

(* ************************************************************************ *)

(* Takes anything that isn't composed of primary unknowns, secondary *)
(* unknowns, or parameters and returns an empty set. *)
SolveStepByStep[___] := {}

(* Takes the equation and primary unknowns (which are either THE primary *)
(* unknowns, THE secondary unknowns, or THE parameters from above).  *)
(* 1. If the equation is polynomial in any of the unknowns, it selects *)
(*    them and sorts them by power/exponent and then includes the unknowns *)
(*    that the equation is not polynomial in.  If the equation is not *)
(*    polynomial in any of the unknowns, it takes the order that they *)
(*    were given in.  *)
(* 2. Uses Reduce to solve the equation (along with find the constraints). *)
(* 3. Then it converts the results to rules (same form as Solve) and *)
(*    returns an empty list if it is empty. *)
(* 4. If there is a solution, it removes a != b type results from the *)
(*    form of the solution outputed by Reduce. *)
(* 5. It then applies the results of the solution to the rest of the *)
(*    solution. *)
(* 6. Formats the solution so that each sublist contains the latest solution *)
(*    branches along with the previous solutions in a flattened and unique *)
(*    list. *)
SubSolveStepByStep[eqn_, primaryunknowns_, pars_, constraints_, sol_] :=
   Block[{a, b, c},
      a = Select[primaryunknowns, PolynomialQ[eqn, #]&];
      If[Length[a] != 0,
         a = Sort[a, Exponent[eqn, #1] <= Exponent[eqn, #2]&];
         a = Flatten[{a, Complement[primaryunknowns, a]}],
         a = primaryunknowns
      ];
      c = Reduce[eqn == 0 && constraints, Flatten[{a, pars}], Sort -> False];
      a = {ToRules[c]};
      If[Length[a] == 0, Return[{}]];
      c = Cases[{#}, p_ != q_, -1]& /@ If[Head[c] === Or, List @@ c, {c}];
      b = Internal`DeactivateMessages[sol /. a, Power::infy, General::indet];
      Union[Transpose[{Flatten /@ Thread[{b, a}, List, 2], c}]]
   ]

(* ************************************************************************ *)

End[] (* `Private` context *)

SetAttributes[AnalyzeAndSolve, ReadProtected]

EndPackage[]

Print["Package PDESpecialSolutions.m was successfully loaded."];

(* ************************************************************************ *)