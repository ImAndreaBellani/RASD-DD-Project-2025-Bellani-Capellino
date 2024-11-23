open util / relation
open util / boolean

sig Tournament {}
// A battle has to belong to exactly one tournament
sig Battle {
belongsTo : one Tournament
}
sig Student {}
// A group is a team of students for a specific battle
sig Group {
participants : set Student ,
battle : Battle
} { participants !=none and cannotEnrollTwiceInABattle }
// We rename it for clarity
sig Score in Int {}
// The submission it is of a specific group and has associated a score
// To represent that submissions are submitted over time we added the submited attribute
sig Submission {
group : one Group ,
score : one Score ,
var submited : one Bool
}{ score>=0 and score<=100 }
// Here we capture the fact that student can enroll only once to any battle if not it
//would be unfair
pred cannotEnrollTwiceInABattle {
all disj g ,h: Group | g. participants & h. participants=none or g . battle!=h. battle
}
// Auxiliary functions used to compute the score :
// Retrieves all the submissions of a group
fun submissions [g: Group ]: set Submission {
( group:>g) . dom  //IL VINCOLO BATTAGLIA - SOTTOMISSIONE per ora NON ESISTE
}
// Retrieves only the submited ones of a group
fun effectiveSubmissions [g: Group ]: set Submission {
{s: g. submissions | s. submited . isTrue }
}
// Calculates all the obtained scores of a group until that moment

fun scores [ g: Group ]: set Score {
g. effectiveSubmissions . score
}
// The best score of a group if it has not submitted it is 0
fun bestScore [g: Group ]: Score {
max [g . scores + {0}] //PERCHE'??? NON MI SEMBRAVA FOSSE DA SPECIFICA
}
// The participants of a tournament in this case it is not necessary to have submitted jus
//to be enrolled ( be part of a group in any of the battles belonging to it )
fun participants [t: Tournament ]: Student {
{s: Student | ( some g: Group | t=g. battle . belongsTo and s in g . participants )}
}
// Score of the student only considering the scores obtained in the battles belonging to
//it
fun scoreInTournament [s: Student , t: Tournament ]: Int {
sum g: s. groupsForATournament [t] | g. bestScore
}
// For the prevoius we need to retrieve the groups in which the student participates
// related to the tournament
fun groupsForATournament [ s: Student , t: Tournament ]: set Group {
{g: Group | s in g . participants and t=g. battle . belongsTo }
}
// Returns the ranking relation for a tournament as previously explained
fun ranking [t: Tournament ]: Student -> Student {
{b , w: t. participants | int b. scoreInTournament [ t]>= int w. scoreInTournament [ t ]}
} //TEORICAMENTE ESISTE PER OGNI STUDENTE "s" L'ISTANZA "(s,s)"

// To model correctly the evolution of the competition we add the following facts :
// The competition begins with 0 effective submissions
fact noSubmissionsAtStart {
all s: Submission | s. submited . isFalse
}
// It ends after all the generated submissions become effective
pred allTournamentsEnd {
eventually all s: Submission | s. submited . isTrue
}
fact { allTournamentsEnd }
// Each step can only submit one submission
pred submit [ s: Submission ]{
submited ’ = submited ++ s -> True
}
fact oneSubmissionPerStep {
always some s: Submission | s. submit
}

run {} for 5 but exactly 2 Submission , 9 int

fact myFact {
	always all s: Submission | s.submited.isFalse implies s.score=0
}
run {
eventually some t: Tournament | #t . participants=2 and symmetric [t. ranking ];
some t: Tournament | antisymmetric [t . ranking ];
some t: Tournament | symmetric [t . ranking ]
} for 3 but exactly 2 Student , 1 Tournament , 9 int
