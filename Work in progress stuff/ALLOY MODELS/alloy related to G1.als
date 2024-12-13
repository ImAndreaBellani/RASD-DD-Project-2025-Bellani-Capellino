/*
	modeling related to G1
	-> there can't be students with the same address
	-> there can't be companies with the same address
	-> students can apply for an internship advice (until the closing deadline)
	-> students can withdraw their application to an internship advice (until the closing deadline)
*/
//date modeling
	sig Date {}
	one sig FirstDay extends Date {} //for uniformity of the concept of "yesterday", the calendar begins with the "MidDay" that has as yesterday the "FirstDay"
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
			all d,d1:MidDay | (d!=d1) implies d.yesterday != d1.yesterday  //a day can't be "the yesterday" of more than one day
			all d:Date | d in MidDay or d in FirstDay //a date or is "MidDay" or is a "FirstDay"
			all d:LastDay | no d1:MidDay |  d1.yesterday = d  //the last day has no tomorrows
			all d:MidDay | d not in d.^(yesterday)  //no "loops" ("a day can't stay before itself in the calendar")
		}
	fact todayFacts //facts to set up "Today"
		{
			all t:Today|t.date in MidDay and t.date.yesterday in FirstDay //the first "Today" is the "MidDay" that has as yesterday the "FirstDay"
		 	always (all t: Today | t.date not in LastDay implies t.date'.yesterday = t.date) //"today" must move in steps "one day after the other"
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
			var date: one Date,
			var advice: one InternshipAdvice,
			var student: one Student
		}
	fact applicationFacts
		{
			always (all a:Application| ((a.advice!=a.advice' or a.student!=a.student') ) implies (some t:Today|a.date'=t.date'))
				//if an application "changes", its date must set to "Today"
			always (all a:Application| ((a.advice=a.advice' and a.student=a.student') ) implies (a.date' = a.date))
				//if an application "does not change", its date must not change
			always (all a:Application| a.date = a.advice.deadline or a.date in a.advice.deadline.^(yesterday))
				//any application must be sent within the advices deadlines
		}
pred show
	{
		all a:Application| some t:Today | a.date = t.date //all pre-simulation applications are submitted in first simulation day
		some a:InternshipAdvice|  a.deadline not in FirstDay //some pre-simulation advices can't have a deadline in "FirstDay"
		always (some a:Application| a.date != a.date') //in this way, at least one application has to "change" each day
		
		#(Application) = 2
		#(InternshipAdvice) = 2
		#(Date) = 5
	}
run show for 5
