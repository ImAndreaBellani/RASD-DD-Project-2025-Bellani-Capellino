/*
	modeling related to G1
	-> there can't be students with the same address
	-> there can't be companies with the same address
	-> students can be apply for an internship advice (until the closing deadline)
	-> students can withdraw their application to an internship advice (until the closing deadline)
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
			var date: one Date,
			var advice: one InternshipAdvice,
			var student: one Student
		}
	fact applicationFacts
		{
			always (all a:Application| (a.date not in FirstDay) implies (a.date' not in a.date.tomorrows)) 
			always (all a:Application| (a.date=a.advice.deadline or a.date not in a.advice.deadline.tomorrows))
			always (all a:Application| ((a.advice!=a.advice' or a.student!=a.student') ) implies (some t:Today|a.date'=t.date'))
		}
	fun tomorrows [d:MidDay] : set Date
		{
			d.^(yesterday)
		}
pred show
	{
		all a:Application | (a.date in FirstDay)
		no i1,i2: InternshipAdvice | i1!=i2 and i1.deadline = i2.deadline
		some a:Application | a.student != a.student'
		always(some i:InternshipAdvice|some t:Today|t.date=i.deadline)
		always (all t:Today|
				t.date' != t.date and
				t.date'' != t.date and t.date'' !=t.date and
				t.date''' != t.date'' and t.date''' != t.date' and t.date''' != t.date and
				t.date'''' != t.date''' and t.date'''' != t.date'' and t.date'''' != t.date' and t.date'''' != t.date)
	}
run show for 5
