from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import IntVar
import ortools
from datetime import date, timedelta
from enum import IntEnum, auto
from functools import partial

class Weekday(IntEnum):
    MONDAY = 0
    TUESDAY = auto()
    WEDNESDAY = auto()
    THURSDAY = auto()
    FRIDAY = auto()
    SATURDAY = auto()
    SUNDAY = auto()

class ResidentSchedulingSolver:
    def __init__(self, 
                 start_date: str = '2024-05-06', 
                 num_days: int = 28, 
                 nofill: list[int] = [], 
                 max_shifts_per_week: int = 1, 
                 extra_friday_penalty: int = 5, 
                 residents_info = None, 
                 holidays: list[int] = [],
                 shifts: list[str] = ['day', 'night'],
                 classification: str = 'junior',
                ) -> None:

        self.classification = classification
        self.num_days = num_days
        self.trauma_shift_multiplier = 2
        self.shifts = shifts
        self.shifts_per_day = len(self.shifts)
        self.max_shifts_per_week = max_shifts_per_week
        self.extra_friday_penalty_amount = extra_friday_penalty
        self.half_day_call_penalty = 2
        self.days = list(range(num_days))
        self.schedules = {}  # To store the schedule of each resident
        if residents_info:
            for resident in residents_info:
                self.add_resident_info(**resident)
        self.nofill = nofill
        self.num_nofill = len(self.nofill)
        self.days_to_fill = self.num_days - len(self.nofill)
        self.start_date = date.fromisoformat(start_date)

        def build_weekday_list(weekday: Weekday):
            return [weekday for weekday in range(weekday, num_days, len(Weekday))]

        mondays = build_weekday_list(Weekday.MONDAY)
        tuesdays = build_weekday_list(Weekday.TUESDAY)
        wednesdays = build_weekday_list(Weekday.WEDNESDAY)
        thursdays = build_weekday_list(Weekday.THURSDAY)
        fridays = build_weekday_list(Weekday.FRIDAY)  # TODO: Anything relative to Friday should probably be associated with the last working day of the week.
        saturdays = build_weekday_list(Weekday.SATURDAY)
        sundays = build_weekday_list(Weekday.SUNDAY)

        weekdays = []
        for days in [mondays, tuesdays, wednesdays, thursdays, fridays]:
            weekdays.extend(days)
        weekends = []
        for days in [saturdays, sundays]:
            weekends.extend(days)
        self.working_days = weekdays.copy()
        self.weekends_and_holidays = weekends.copy()
        if holidays:
            for holiday in holidays:
                self.add_holiday(holiday)
        
        self.model = cp_model.CpModel()
    
    def assign_claimed_days(self, resident):
        """
        For any person and shift listed in 'claimed_days', assign that individual to that shift.
        """
        for day, shift in resident['claimed_days']:
            try:
                self.model.Add(self.schedules[resident['name']][day][shift] == 1)
            except Exception as e:
                print("{resident=}\n{day=}\n{shift=}")
                raise e

    def add_holiday(self, day: int):
        """
        Add a holiday to use in the weekend/weekday ratio calculations.
        remove the holiday from the working_days list and add it to the weekends_and_holidays list
        """
        self.working_days.remove(day)
        self.weekends_and_holidays.append(day)
        self.working_days.sort()
        self.weekends_and_holidays.sort()

    def add_resident_info(self, 
                          name: str, 
                          on_vacation_days: list[int] = [], 
                          on_trauma: bool = False, 
                          on_emergency: bool = False, 
                          days_override = None, 
                          claimed_days: list[tuple[int, str]] = []):
        """
        Create a resident entry to include in the schedule.
        """
        if not hasattr(self, 'residents_info'):
            self.residents_info = []
        on_vacation_days = on_vacation_days
        for day in self.nofill:
            try:
                on_vacation_days.remove(day)
            except:
                pass
        self.residents_info.append({
            "name": name,
            "on_vacation_days": on_vacation_days,
            "on_trauma": on_trauma,
            "on_emergency": on_emergency,
            "days_override": days_override,
            "claimed_days": claimed_days,
        })
        self.calculate_call_ratio()

    def calculate_call_ratio(self):
        """
        Calculate the call ratio to apply across all residents.  This call ratio is based on the number of call days relative to the number of person-days.  
        This calculation also provides an increase based on which residents are assigned to the trauma department.
        """
        # \sigma (1 + t * (c - 1)) * (D - V)
        resident_days_available = sum(
            [
                (1 + int(resident['on_trauma']) * (self.trauma_shift_multiplier - 1)) 
                * 
                (self.days_to_fill - len(resident['on_vacation_days'])) 
            for resident in self.residents_info]
        )
        self.call_ratio = self.days_to_fill / resident_days_available
        # print(f"Call ratio determined to be: {self.call_ratio}")

    def strictly_bounded(self, resident, calculation, lower_bound: int, upper_bound: int, bounded_descriptor: str=""):
        """
        Make sure that [calculation] is between [lower] and [upper] bounds.  Use [Bounded descriptor] for any field labeling
        @param calculation: The result of the calculation that would go into a NewIntVar type from OR-tools.
        @param lower_bound: An integer representing the lowest possible value.  This value will receive a penalty of 1 if it is reached.
        @param upper_bound: An integer representing the highest possible value.  This value will receive a penalty of 1 if it is reached.
        @param bounded_descriptor: A string to signify the type of bound that is being established.  This must be unique.
        """
        print(f"Target {bounded_descriptor} for {resident['name']}: {lower_bound} < x < {upper_bound}")
        shifts_taken = self.model.NewIntVar(0, len(self.days), f"{bounded_descriptor}_taken_{resident['name']}")
        lower_bound_reached = self.model.NewBoolVar(f"{bounded_descriptor}_lower_bound_{resident['name']}")
        upper_bound_reached = self.model.NewBoolVar(f"{bounded_descriptor}_upper_bound_{resident['name']}")
        self.model.Add(shifts_taken == calculation)
        self.model.Add(shifts_taken >= lower_bound)
        self.model.Add(shifts_taken <= upper_bound)
        self.model.Add(shifts_taken == lower_bound).OnlyEnforceIf(lower_bound_reached)
        self.model.Add(shifts_taken == upper_bound).OnlyEnforceIf(upper_bound_reached)
        self.model.Add(shifts_taken != lower_bound).OnlyEnforceIf(lower_bound_reached.Not())
        self.model.Add(shifts_taken != upper_bound).OnlyEnforceIf(upper_bound_reached.Not())
        self.penalties.append(lower_bound_reached)
        self.penalties.append(upper_bound_reached)

    def balance_trauma_call(self, resident):
        """
        Weekday call can only be filled by trauma residents.  
        This method ensures that call assigned to the trauma residents is equitably distributed.
        """
        num_trauma_days = len(self.working_days)
        trauma_days_available = 0
        num_trauma_residents = 0
        for tr_resident in self.residents_info:
            if tr_resident['on_trauma']:
                num_trauma_residents += 1
                for day in self.working_days:
                    if day not in tr_resident['on_vacation_days']:
                        trauma_days_available += 1
        trauma_days_ratio = num_trauma_days / trauma_days_available
        num_away_days = 0
        for day in self.days:
            if day in resident['on_vacation_days']:
                num_away_days += 1
        for day in self.working_days:
            if day not in resident['on_vacation_days']:
                expected_day_shifts = (num_trauma_days - num_away_days) \
                                            * trauma_days_ratio
        trauma_upper_bound = int(expected_day_shifts + 1)
        trauma_lower_bound = int(expected_day_shifts - 1)
        self.strictly_bounded(
            resident,
            calculation=sum(self.schedules[resident['name']][day][self.shifts[0]] for day in self.working_days),
            lower_bound=trauma_lower_bound,
            upper_bound=trauma_upper_bound,
            bounded_descriptor="trauma_shifts"
        )

    def emergency_wednesday_halfday(self, resident):
        """
        Residents on rotation from emergency have academic half-days on Wednesdays.  They cannot be on call during their half-day.
        """
        # If on rotation from emergency, cannot be on call on Wednesdays
        if resident["on_emergency"]:
            for day in [day for day in self.working_days if day % len(Weekday) == Weekday.WEDNESDAY]:
                for shift in self.shifts:
                    self.model.Add(self.schedules[resident['name']][day][shift] == 0)

    def trauma_day_call(self, resident):
        """
        Only residents on the trauma rotation can be on call during the day.  Other residents will have other priorities in departments outside of trauma.
        """
        # Only residents on trauma rotation can work day-call
        if not resident["on_trauma"]:
            for day in self.working_days:
                self.model.Add(self.schedules[resident['name']][day][self.shifts[0]] == 0)

    def post_call_days(self, resident, ignore: int = None):
        """
        Residents will generally not be on call two days in a row.  The exception to this is senior residents who will generally have Friday and Saturday paired together.
        """
        # Prevent call on the day following a night shift
        name = resident['name']
        for day in range(self.num_days - 1):
            if day % 7 != ignore:
                for shift in self.shifts:
                    self.model.AddAtMostOne(self.schedules[name][day]    [self.shifts[-1]],
                                            self.schedules[name][day + 1][shift]
                                            )

    def prefer_full_day_call(self, resident):
        """
        Ideally, a resident will complete a full day of call, rather than having shifts more dispersed.
        This currently only works on days that have 2 shifts.  Anything more will not work.
        """
        name = resident['name']
        for day in self.days:
            full_day_preference_violated = self.model.NewBoolVar(f'full_day_{name}_{day}')
            half_day_penalty = self.model.NewIntVar(0, 16, f"penalty_{name}_halfday_{day}")
            # self.model.AddBoolAnd([self.schedules[name][day][shift] for shift in self.shifts]).OnlyEnforceIf(full_day_preference_violated.Not())
            self.model.AddBoolXOr([
                self.schedules[name][day][self.shifts[0]], #TODO: Make this accept an arbitrary number of shifts
                self.schedules[name][day][self.shifts[-1]], 
                full_day_preference_violated.Not()])  # If morning or evening call but not both, trigger penalty.  Function does not support "OnlyEnforceIf", so we need to place the control boolean inside of the XOr
            self.model.Add(half_day_penalty >= self.half_day_call_penalty).OnlyEnforceIf(full_day_preference_violated)
            self.penalties.append(half_day_penalty)

    def friday_implies_sunday(self, resident):
        """
        Evening call on Friday will result in call on Sunday.
        """
        for day in self.days:
            if day % 7 == Weekday.FRIDAY:  # FOR JUNIORS ONLY: Friday night implies Sunday FULL DAY call as well
                for shift in self.shifts:
                    self.model.AddImplication(self.schedules[resident['name']][day]  [self.shifts[-1]], 
                                              self.schedules[resident['name']][day+2][shift])

    def friday_implies_saturday(self, resident):
        """
        Evening call on Friday will result in call on Saturday.
        """
        for day in self.days:
            if day % 7 == Weekday.FRIDAY:
                for shift in self.shifts:
                    self.model.AddImplication(self.schedules[resident['name']][day]  [self.shifts[-1]], 
                                              self.schedules[resident['name']][day+1][shift])

    def multiday_implication(self, resident, first, second):
        """
        If the first day is taken, ensure they fill the second shift as well.
        """
        day_gap = (second - first) % 7
        for day in self.days:
            if day % 7 == first:
                for shift in self.shifts:
                    self.model.AddImplication(self.schedules[resident['name']][day]          [self.shifts[-1]], 
                                              self.schedules[resident['name']][day + day_gap][shift])

    def penalize_multiple_fridays(self, resident):
        """
        Friday call is very disruptive to weekends, especially given the implied multi-day call.  Add a penalty to discourage assignment of multiple fridays.
        """
        name = resident['name']
        for friday in [day for day in self.days if day % 7 == Weekday.FRIDAY]:
            other_friday = friday + len(Weekday)
            if other_friday not in self.days:
                continue
            friday_conflict = self.model.NewBoolVar(f"{name}_Fridays_{friday}_{other_friday}")
            friday_penalty = self.model.NewIntVar(0, 16, f"penalty_{name}_Fridays_{friday}_{other_friday}")
            self.model.AddBoolAnd(
                self.schedules[name][friday]      [self.shifts[-1]], 
                self.schedules[name][other_friday][self.shifts[-1]]
                ).OnlyEnforceIf(friday_conflict)  # If both items are assigned, then friday_conflicts will be positive.
            # self.model.AddBoolOr(
            #     self.schedules[name][friday]      [self.shifts[-1]].Not(), 
            #     self.schedules[name][other_friday][self.shifts[-1]].Not()
            #     ).OnlyEnforceIf(friday_conflict.Not())  # If either friday does not conflict, then at least one must be not booked.
            self.model.Add(friday_penalty >= self.extra_friday_penalty_amount).OnlyEnforceIf(friday_conflict)
            self.penalties.append(friday_penalty)

    def disperse_call(self, resident):
        """
        Assign a penalty if there are more than "max_shifts_per_week" in a given week.  This penalty scales based on the current number of shifts assigned.
        """
        name = resident['name']
        # Divide the schedule into 4 weeks and try to limit number of calls per week to self.max_days_per_week
        for week in range(self.num_days//len(Weekday)):
            start_day = week * 7
            end_day = start_day + 7
            weekly_calls = sum(self.schedules[name][day][am_pm] for day in range(start_day, end_day) for am_pm in self.shifts)
            exceeds_max_calls = self.model.NewBoolVar(f"{name}_week_{week}_exceeds_max")
            self.model.Add(weekly_calls <= self.max_shifts_per_week).OnlyEnforceIf(exceeds_max_calls.Not())
            self.model.Add(weekly_calls > self.max_shifts_per_week).OnlyEnforceIf(exceeds_max_calls)

            weekly_penalty = self.model.NewIntVar(0, 7, f"Week_{week}_penalty_{name}")

            # penalize going over the max days per week, but don't fully restrict it.
            for i in range(self.max_shifts_per_week + 1, 7):
                weekly_exceeds_i = self.model.NewBoolVar(f"Week_{week}_penalty_{name}_exceeds_{i}")
                self.model.Add(weekly_calls >= i).OnlyEnforceIf(weekly_exceeds_i)
                self.model.Add(weekly_penalty >= 2 * i).OnlyEnforceIf(weekly_exceeds_i)
                self.penalties.append(weekly_penalty)
            # weekly_calls = max(0, weekly_calls - 2)
            # self.model.Add(weekly_penalty == weekly_calls)
            # # penalty = self.model.NewIntVar(0, 2**4, f"Week {week} penalty for {name}")
            # # self.model.Add(penalty == weekly_calls)

    def set_shift_expectations(self, resident):
        """
        Use precalculated call ratio to determine how many total shifts, and weekend shifts a given resident should have.  Assign bounds of +1 and -1 from this number to allow some flexibility.
        """
        if resident['days_override']:
            expected_night_shifts = resident['days_override']
        else:
            expected_night_shifts = (len(self.days) - len(resident['on_vacation_days'])) \
                                    * self.call_ratio \
                                    * (self.trauma_shift_multiplier if resident['on_trauma'] else 1)
                                    # * self.shifts_per_day \
        lower_bound = int(expected_night_shifts - 1)
        upper_bound = int(expected_night_shifts + 1)

        print(f"Expected shifts for {resident['name']}: {expected_night_shifts}")
        self.strictly_bounded(
            resident=resident,
            calculation=sum(self.schedules[resident['name']][day][self.shifts[-1]] for day in self.days),
            lower_bound=lower_bound,
            upper_bound=upper_bound,
            bounded_descriptor="total_shifts"
        )

        # Try to keep weekends equitably distributed.  Penalize deviations
        expected_weekend_shifts = expected_night_shifts * 2/7
        weekend_upper_bound = int(expected_weekend_shifts + 1)
        weekend_lower_bound = int(expected_weekend_shifts - 1)

        self.strictly_bounded(
            resident=resident,
            calculation=sum(self.schedules[resident['name']][day][self.shifts[0]] for day in self.weekends_and_holidays),
            lower_bound=weekend_lower_bound,
            upper_bound=weekend_upper_bound,
            bounded_descriptor="weekend_shift"
        )

    def cant_book_vacation_days(self, resident):
        """
        Residents on vacation cannot be put on call.
        """
        # If on vacation, cannot be on call
        for day in self.days:
            if day in resident["on_vacation_days"]:
                for shift in self.shifts:
                    self.model.Add(self.schedules[resident['name']][day][shift] == 0)
    
    def cant_book_nofill_days(self, resident):
        for day in self.nofill:
            for shift in self.shifts:
                self.model.Add(self.schedules[resident['name']][day][shift] == 0)

    def add_resident_model(self, resident, build_functions: list):
        """
        Add fields to the model based on the attributes of the resident provided in the resident parameter, and apply to functions passed through the "build_functions" parameter.
        """
        name = resident["name"]
        self.schedules[name] = [
            {shift: self.model.NewBoolVar(f'call_{name}_{day}_{shift}') for shift in self.shifts} for day in self.days
        ]

        for func in build_functions:
            func(resident)

        # Balance trauma resident day call shifts
        if resident['on_trauma'] and self.classification == 'junior':
            self.balance_trauma_call(resident)

    def setup_model(self):
        # Create a schedule variable for each resident for each day
        self.penalties = []

        junior_build_functions = [
            self.emergency_wednesday_halfday, 
            self.cant_book_vacation_days,
            self.trauma_day_call, 
            self.post_call_days, 
            self.prefer_full_day_call,
            self.penalize_multiple_fridays,
            self.disperse_call, 
            self.set_shift_expectations,
            self.friday_implies_sunday,
            self.assign_claimed_days,
        ]

        senior_build_functions = [
            self.cant_book_vacation_days,
            partial(self.post_call_days, ignore=Weekday.FRIDAY),
            self.penalize_multiple_fridays,
            self.disperse_call,
            self.set_shift_expectations,
            self.friday_implies_saturday,
            self.assign_claimed_days,
        ]

        if self.classification == 'junior':
            build_functions = junior_build_functions
        elif self.classification == 'senior':
            build_functions = senior_build_functions

        for resident in self.residents_info:
            self.add_resident_model(resident, build_functions)

        # There must be a resident on shift
        for day in self.days:
            if day not in self.nofill:
                for shift in self.shifts:
                    self.model.AddExactlyOne([self.schedules[resident['name']][day][shift] for resident in self.residents_info])

        # Try to avoid penalizing aspects of schedules
        self.model.Minimize(sum(self.penalties))

    def solve(self):
        self.solver = cp_model.CpSolver()
        status = self.solver.Solve(self.model)
        if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
            print("Solution found!")
        else:
            print("No solution available.")
        self.status = status

    def print_schedule(self):
        if self.status == cp_model.OPTIMAL or self.status == cp_model.FEASIBLE:
            for name, schedule in self.schedules.items():
                print(f"Shifts for {name:12}: ", end="")
                for shift in self.shifts:
                    print(f"{shift} shift: {sum(self.solver.BooleanValue(day[shift]) for day in schedule):02}    ", end="")
                print(f"Weekend: {sum(self.solver.BooleanValue(schedule[day][self.shifts[0]]) for day in self.weekends_and_holidays)}")
                # print(f"{self.shifts[-1]} shifts for {name}: {sum(self.solver.BooleanValue(day[self.shifts[-1]]) for day in schedule)}")
                # print(f"{self.shifts[0]} shifts for {name}: {sum(self.solver.BooleanValue(day[self.shifts[0]]) for day in schedule)}")
                # print(f"{bounds[name][0]}: {self.solver.Value(bounds[name][0])} - {bounds[name][1]}: {self.solver.Value(bounds[name][1])}")

            print("        ")
            # for name in self.schedules.keys():
            #     print(f"{name:12}", end="")
            # print("")

            # for day in self.days:
            #     adjusted_day = self.start_date + timedelta(day)
            #     for am_pm in self.shifts:
            #         print(f"{adjusted_day.strftime('%b%d')}{am_pm} ", end="")
            #         for name in self.schedules.keys():
            #             if self.solver.BooleanValue(self.schedules[name][day][am_pm]):
            #                 print(f"{name:12}", end="")
            #             else:
            #                 print("            ", end="")
            #         print("")
            print(f"Total loss: {self.solver.ObjectiveValue()}")
            print(f"Total loss: {self.solver.SolutionInfo()}")

            for week in range(self.num_days//len(Weekday)):
                print("\n")
                for day in range(week * len(Weekday), (week + 1) * len(Weekday)):
                    adjusted_day = self.start_date + timedelta(day)
                    print(f"{adjusted_day.strftime('%b%d'):12}", end="")
                print("")
                for shift in self.shifts:
                    for day in range(week * len(Weekday), (week + 1) * len(Weekday)):
                        found_person = False
                        for name in self.schedules.keys():
                            try:
                                if self.solver.BooleanValue(self.schedules[name][day][shift]):
                                    print(f"{name:12}", end="")
                                    found_person = True
                            except Exception as e:
                                # print(f"{day=}{shift=}{name=}")
                                pass
                        if not found_person:
                            print("            ", end="")
                    print("")
                # for day in range(week * 7, (week + 1) * 7):
                #     found_person = False
                #     for name in self.schedules.keys():
                #         if self.solver.BooleanValue(self.schedules[name][day]['pm']):
                #             print(f"{name:12}", end="")
                #             found_person = True
                #     if not found_person:
                #         print("            ", end="")
            print("")

if True:
    ## Senior block 11
    senior_solver = ResidentSchedulingSolver(
        start_date='2024-04-08',
        classification='senior',
        shifts=['night']
    )
    senior_solver.add_resident_info("P", [date for date in range(10, 21)])
    senior_solver.add_resident_info("R", [date for date in range(19, 29)])
    senior_solver.add_resident_info("H", [date for date in range(5, 21)])
    senior_solver.add_resident_info("S", [date for date in range(18, 29)], on_trauma=True, claimed_days=[(11, 'night')])
    senior_solver.add_resident_info("M", [date for date in range(0, 13)], on_trauma=True)  # date for date in range(0, 13)
    senior_solver.add_resident_info("A")
    senior_solver.add_resident_info("K", [0, 1, 5, 6, 17, 25, 26, 27], on_trauma=True)
    senior_solver.setup_model()
    senior_solver.solve()
    senior_solver.print_schedule()

if True:
    ## Senior Block 12
    senior_solver = ResidentSchedulingSolver(
        classification='senior',
        shifts=['night']
    )
    r5_study_break = [date for date in range(9, 17)]
    r5_study_break.append(3)
    a_vacation = r5_study_break.copy()
    a_vacation.extend(range(23, 29))
    senior_solver.add_resident_info("P")
    senior_solver.add_resident_info("R")
    senior_solver.add_resident_info("H")
    senior_solver.add_resident_info("S", r5_study_break, on_trauma=True, claimed_days=[(25, 'night'), (26, 'night')])
    senior_solver.add_resident_info("M", r5_study_break, on_trauma=True)  # date for date in range(0, 13)
    senior_solver.add_resident_info("N", r5_study_break)
    senior_solver.add_resident_info("A", a_vacation)
    senior_solver.setup_model()
    senior_solver.solve()
    senior_solver.print_schedule()

if True:
    junior_solver = ResidentSchedulingSolver(nofill=[5, 12, 23])  
            # H is very restricted in call.  It's easier to no-fill the days that H will be on call and then 
            # manually select another person to pair them with.  There's also a day where no trauma residents 
            # are available for the day-call shift and this shift will need to be filled by a senior resident.
    junior_solver.add_resident_info("C", [23], on_trauma=True)
    junior_solver.add_resident_info("R", [0, 1, 2, 3, 4, 5, 6, 12, 23], on_trauma=True)
    junior_solver.add_resident_info("A", [12, 13, 14])
    junior_solver.add_resident_info("Mh")
    # junior_solver.add_resident_info("H", [date for date in range(19, 29)])
    junior_solver.add_resident_info("K")
    junior_solver.add_resident_info("Mk", [date for date in range(5, 14)])
    junior_solver.setup_model()
    junior_solver.solve()
    junior_solver.print_schedule()
    
