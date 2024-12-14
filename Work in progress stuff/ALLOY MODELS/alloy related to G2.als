/*
	modeling related to G2
*/
//date modeling
	sig Date {}
	one sig FirstDay extends Date {} //for uniformity of the concept of "yesterday", the calendar begins with the "MidDay" that has as yesterday the "FirstDay"
	sig MidDay extends Date
		{
			yesterday: one Date
		}
	one sig LastDay extends MidDay {}
	fact calendar //facts to design the "date chain"
		{
			all d,d1:MidDay | (d!=d1) implies d.yesterday != d1.yesterday  //a day can't be "the yesterday" of more than one day
			all d:Date | d in MidDay or d in FirstDay //a date or is "MidDay" or is a "FirstDay"
			all d:LastDay | no d1:MidDay |  d1.yesterday = d  //the last day has no tomorrows
			all d:MidDay | d not in d.^(yesterday)  //no "loops" ("a day can't stay before itself in the calendar")
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
	fact applicationFacts
		{
			all a:Application| a.date = a.advice.deadline or a.date in a.advice.deadline.^(yesterday)
				//any application must be sent within the advices deadlines
		}
//selection processes modeling
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
			all f1,f2:FirstStep|(f1.process = f2.process) implies (f1 = f2)
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
		}
	fact selectionFacts
		{
			all s:Student |(all iv:Interview | (s = iv.student) iff (some a:Application|s in a.student and iv.step.process.advice=a.advice))
				//only student applied for an advice can take part into the selection process related to that advice
			all i:Interview| i.date  in i.step.process.advice.deadline.^yesterday
				//an interview can't be put in a date before the deadline advice
			all i,i1:Interview | (i.step.process = i1.step.process and i!=i1 and i.step in i1.step.^previousStep) implies (i.date in i1.date.^yesterday)
				//two interviews (of the same process) must have dates that "respect" the order of the selection process
			no s1,s2:SelectionProcess|s1!=s2 and s1.advice = s2.advice
				//like one selection process is related to an advice, an advice can't have more than one selection process related
			all s1:SelectionStep| s1 not in FirstStep implies s1.process = s1.previousStep.process
				//a selection steps "chain" must belong to one selectionStep
			all i,i1:Interview| (i!=i1 and i.student = i1.student) implies (i.step != i1.step)
				//a step has only one interview for each student that take part into the process
			all s:Student| (some i:Interview|i.student = s) implies (some a:Application|a.student = s)
				//a student enrolled in a selection process must have an application for the related advice
		}
pred show
	{
		#(Application) = 2
		#(InternshipAdvice) = 2
		#(Date) = 3
	}
run show for 5

