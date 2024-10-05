import datetime
from monthly_schedule import ResidentSchedulingSolver, Weekday

def print_possible_dates(start_date: datetime.date, num_days: int, unavailable: list[int] = []):
    """
    Print out a calendar showing available dates to schedule.
    @param start_date: 
    """
    for week in range(num_days//len(Weekday)):
        print("\n")
        for day in range(week * len(Weekday), (week + 1) * len(Weekday)):
            adjusted_day = start_date + datetime.timedelta(day)
            print(f"{adjusted_day.strftime('%b%d'):12}", end="")
        print("")
        for day in range(week * len(Weekday), (week + 1) * len(Weekday)):
            print(f"{day:4}        ", end="") if day not in unavailable else print("            ", end="")
        print("")
    print("")

def simple_parse(data_type: type, parse_func, input_string: str, error_string: str):
    var = '' if data_type != str else 0
    while type(var) != data_type:
        try:
            var = parse_func(input(input_string))
        except TypeError:
            print(error_string)
    return var

def classification_validation(classification: str):
    if classification.lower() in ['junior', 'senior']:
        return classification.lower()
    if classification.lower() == 'j':
        return 'junior'
    if classification.lower() == 's':
        return 'senior'
    else:
        raise(TypeError)

def comma_str(content: str):
    if len(content) == 0:
        return []
    return list(map(lambda string: string.strip(), content.split(',')))

def comma_int(content: str):
    if len(content) == 0:
        return []
    return list(map(int, content.split(',')))

start_date = simple_parse(datetime.date, 
                          datetime.date.fromisoformat, 
                          "What date would you like to begin your schedule on? [yyyy-mm-dd]  ", 
                          "Error parsing string.  Please use the format 'yyyy-mm-dd'")

num_days = simple_parse(int, 
                        int, 
                        "Please enter the number of days to schedule:  ", 
                        "Error parsing value, please enter an integer")

end_date = start_date + datetime.timedelta(num_days)

num_days = (end_date - start_date).days

nofill = []
for day in range(start_date.weekday()):
    nofill.append(day)

start_date = start_date - datetime.timedelta(start_date.weekday())

classication = simple_parse(str, 
                            classification_validation, 
                            "Please choose either junior or senior as your classification [J/S]:  ", 
                            'Error: please enter junior or senior')

shifts = simple_parse(list, 
                      comma_str, 
                      "Please enter a comma separated list of daily shifts ['day, night']:  ", 
                      "error processing comma list")

print_possible_dates(start_date, num_days, unavailable=nofill)

more_no_fill = simple_parse(list, 
                            comma_int, 
                            "Please enter the indexes of dates you would not like to fill ['13, 20']:  ", 
                            "Error processing comma list")

nofill.extend(more_no_fill)

schedulable_people = simple_parse(int, 
                                  int, 
                                  "How many people would you like to schedule?  ", 
                                  "Error parsing value.  Please enter an integer.")

residents = []

for i in range(schedulable_people):
    resident = {}
    resident['name'] = (input(f"Enter the name of resident {i + 1}:  "))
    trauma = ''
    while type(trauma) != bool:
        trauma = input(f"Is {resident['name']} on their trauma rotation? [Y/N]  ")
        if trauma[0] in 'YyTt':
            trauma = True
        elif trauma[0] in 'NnFf':
            trauma = False
        resident['on_trauma'] = trauma

    emergency = ''
    while type(emergency) != bool:
        emergency = input(f"Is {resident['name']} on rotation from the emergency department?  [Y/N]")
        if emergency[0] in 'YyTt':
            emergency = True
        elif emergency[0] in 'NnFf':
            emergency = False
        resident['on_emergency'] = emergency

    residents.append(resident)

print_possible_dates(start_date, num_days, unavailable=nofill)

for resident in residents:
    resident['on_vacation_days'] = simple_parse(list, comma_int, f"please select vacation days for {resident['name']} [5, 6, 7, 12, 14]  ", "Error parsing values")
    resident['days_override'] = None #  simple_parse(list, comma_int, f"please provide override days:", "Error processing list  ")
    resident['claimed_days'] = simple_parse(list, comma_int, "Claim days: ", "error parsing list  ")

solver = ResidentSchedulingSolver(start_date=start_date.isoformat(), 
                                  num_days=num_days, 
                                  nofill=nofill, 
                                  residents_info=residents, 
                                  shifts=shifts,
                                  classification=classication, )

# print(f"""ResidentSchedulingSolver({start_date.isoformat()},
#       {num_days=},
#       {nofill=},
#       {shifts=},
#       {classication=},
#       {residents=})""")

solver.setup_model()
solver.solve()
solver.print_schedule()
    