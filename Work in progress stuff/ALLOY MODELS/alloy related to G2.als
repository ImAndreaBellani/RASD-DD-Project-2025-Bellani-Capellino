/*
	modeling related to G2
	-> companies can set up a selection process
	-> only students who enrolled the selection process can be selected or rejected by the company
*/
//date modeling
	sig Date {}
	one sig FirstDay extends Date {}
	sig MidDay extends Date
		{
			yesterday: one Date
		}
	one sig LastDay extends MidDay {}
	one sig Today
		{
			var date: one Date
		}
	fact calendar //facts to design the "date chain"
		{
			all d,d1:MidDay | (d!=d1) implies d.yesterday != d1.yesterday
			all d:Date | d in MidDay or d in FirstDay
			all d:LastDay | no d1:MidDay |  d1.yesterday = d
			all d:MidDay | d not in d.^(yesterday)
		}
	fact todayFacts //facts to set up "Today"
		{
			all t:Today|t.date in FirstDay
			always (all t:Today|t.date' not in FirstDay implies t.date in t.date'.yesterday)	
		}
//profiles modeling
	sig Mail  {}
	sig Profile
		{
			mail: one Mail
		}
	sig Student extends Profile {}
	sig Company extends Profile{}
	fact register
		{
			all p: Profile | p in Company or p in Student
		}
	fact noDuplicateMails
		{
    			all p1, p2: Profile | (p1 != p2) implies (p1.mail != p2.mail)
		}
//application modeling
	sig InternshipAdvice
		{
			company: one Company,
			deadline: one Date
		}
	sig Application
		{
			date: one Date,
			advice: one InternshipAdvice,
			student: one Student
		}
//selection processes modeling
	sig Score {}
	sig SelectionProcess
		{
			advice: one InternshipAdvice
		}
	sig SelectionStep
		{
			process: one SelectionProcess
		}
	sig FirstStep extends SelectionStep {}
	sig MidStep extends SelectionStep
		{
			previousStep: one SelectionStep
		}
	one sig LastStep extends MidStep {}
	fact selectionCalendar //facts to design the "selection process"
		{
			all d,d1:MidStep | (d!=d1) implies d.previousStep != d1.previousStep
			all d:SelectionStep | d in MidStep or d in FirstStep
			all d:LastStep | no d1:MidStep |  d1.previousStep = d
			all d:MidStep | d not in d.^(previousStep)
		}
	sig Interview
		{
			date: one Date,
			step: one SelectionStep,
			student: one Student,
			score: one Score //(simplified)
		}
	fact selectionFacts
		{
			always (all s:Student |(all iv:Interview | (s in iv.student) iff (some a:Application|s in a.student and iv.step.process.advice=a.advice)))
			always (all i:Interview|(i.date= i.step.process.advice.deadline or i.date in i.step.process.advice.deadline.tomorrows))
					always (all s:Student| (all i,i1:Interview | (i.student=s and i1.student=s and i!=i1 and i.date in i1.date.tomorrows) implies (i1.step not in i.step.nextSteps)))
			always (no s1,s2:FirstStep|s1!=s2 and s1.process.advice = s2.process.advice)
			always (no s1,s2:SelectionProcess|s1!=s2 and s1.advice = s2.advice)
		}
	fun tomorrows [d:MidDay] : set Date
		{
			d.^(yesterday)
		}
	fun nextSteps [d:MidStep] : set SelectionStep
		{
			d.^(previousStep)
		}
pred show
	{
		all a:Application | (a.date in FirstDay)
		always (all t:Today|
				t.date' != t.date and
				t.date'' != t.date and t.date'' !=t.date)// and
			//	t.date''' != t.date'' and t.date''' != t.date' and t.date''' != t.date)// and
			//	t.date'''' != t.date''' and t.date'''' != t.date'' and t.date'''' != t.date' and t.date'''' != t.date)

	}
run show for 3

