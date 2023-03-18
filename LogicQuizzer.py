# Written by Stephen Chen at 2023.02.25
# Edited by Christy on 2023.03.16
import random
import sys
import tkinter
import tkinter as tk
from time import sleep
from tkinter import VERTICAL
from tkinter.messagebox import *
import re as regular 
from sympy.parsing.sympy_parser import parse_expr
import sympy.abc
import sympy
from sympy.logic.boolalg import to_dnf, is_dnf
from sympy.logic.inference import satisfiable, valid
import re


window_color = "#BBDEFB"
teacher = "Teacher"
student = "Student"
append = "APPEND"
test = "TEST"
practice = "PRACTICE"
question_file_name = "questions.txt"
TIME_EXPECTED_FOR_A_QUESTION = 60


# put the window to the center of screen
def center_window(window, w, h):
    ws = root.winfo_screenwidth()
    hs = root.winfo_screenheight()
    # calculate x, y positions
    x = (ws / 2) - (w / 2)
    y = (hs / 2) - (h / 2)
    window.geometry('%dx%d+%d+%d' % (w, h, x, y))

# Create a new subclass of BlueLabel with the default background color set to blue
class BlueLabel(tk.Label):
    def __init__(self, master=None, **kwargs):
        super().__init__(master, **kwargs)
        self.configure(bg=window_color, fg = "black")
        self.configure(font=("Courier New", 20))
        self.pack(pady=(30,0))

class Button(tk.Button):
    def __init__(self, master=None, **kwargs):
        super().__init__(master, **kwargs)
        self.configure(bg=window_color, fg = "black")
        self.configure(font=("Courier New",18))
        self.pack(pady=(15,0))

class radioButton(tk.Radiobutton):
    def __init__(self, master=None, **kwargs):
        super().__init__(master, **kwargs)
        self.configure(bg=window_color, fg = "black")
        self.configure(font=("Courier New",25))
        self.pack(pady=(50,0))

        
class LogicQuizzer:
    def __init__(self, root):
        # Global
        self.start_window = root  # window for start
        self.question_ui = None  # window for question and answer also for appending question
        self.question_type_var = None  # question type been selected
        self.current_user_type = None  # String; store current user type
        self.user_type_var = None  # tk.StringVar(); used to store usr typing for their type
        self.user_types = [teacher, student]

        self.question_mode_var = None  # tk.StringVar(), used to store "TEST" or "PRACTICE"
        self.question_modes = [append, test, practice]
        self.mode = None

        self.num_question_var = None
        self.num_can_be_chosen = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        self.num_of_question = 0

        self.required_type = None  # question type required by user
        # define question type and corresponding solution
        self.question_types = {
            "Truth Table": self.show_truth_table,
            "DNF Form": self.convert_to_dnf,
            "Satisfiability": self.check_satisfiability,
            "Validity": self.check_validity,
        }

        # Student window
        self.question_content_label = None  # question content
        self.status_label = None  # question "Correct" or not
        self.answer_entry = None  # tk.text to enable multiple lines entry
        self.correct_answer = None  # correct answer
        self.questions = {}  # all the question
        self.current_question = None  # current question tuple([0]: type, [1]: content, [2]: formula)
        self.current_question_index = 0  # current question index
        self.remaining_time_var = None
        self.timer = None

        self.test_result = []
        # Teacher window
        self.submit_label = None  # Question written into file successfully or not
        # self.formula_var = None  # Store formula user typed in
        # self.question_var = None  # Store question content user typed in
        self.formula_entry = None  # Store formula user typed in
        self.content_entry = None  # Store question content user typed in

        self.satisfiability_var = tk.StringVar()
        self.validity_var = tk.StringVar()

        self.invalid_input=None
        self.table_error = None


    # Create start window
    def start(self):
        self.start_window.title("Propositional Logic Quizzer")
        self.start_window.configure(bg=window_color)
        center_window(self.start_window, window_width, window_height)


        select_type_label = BlueLabel(self.start_window, text="Who are you:")
        select_type_label.pack()

        self.user_type_var = tk.StringVar()
        self.user_type_var.set(self.user_types[0])

        user_type_manu = tk.OptionMenu(self.start_window, self.user_type_var, *self.user_types)
        user_type_manu.pack(pady=(25,0))
        user_type_manu.config(bg=window_color, fg = "black")

        select_type_label = BlueLabel(self.start_window, text="Select question type:")
        select_type_label.pack()

        self.question_type_var = tk.StringVar()
        self.question_type_var.set(list(self.question_types.keys())[0])
        question_type_menu = tk.OptionMenu(self.start_window, self.question_type_var, *self.question_types.keys())
        question_type_menu.pack(pady=(25,0))
        question_type_menu.config(bg=window_color, fg = "black")

        select_num_label = BlueLabel(self.start_window, text="Select number of question:")
        select_num_label.pack()

        self.num_question_var = tk.StringVar()
        self.num_question_var.set(self.num_can_be_chosen[0].__str__())
        question_num_manu = tk.OptionMenu(self.start_window, self.num_question_var, *self.num_can_be_chosen)
        question_num_manu.pack(pady=(25,0))
        question_num_manu.config(bg=window_color, fg = "black")
        #question_num_manu["menu"].config(bg=window_color)

        select_mode_label = BlueLabel(self.start_window, text="Select mode:", bg= window_color)
        select_mode_label.pack()

        self.question_mode_var = tk.StringVar()
        self.question_mode_var.set(self.question_modes[0])
        question_mode_menu = tk.OptionMenu(self.start_window, self.question_mode_var, *self.question_modes)
        question_mode_menu.pack(pady=(25,70))
        question_mode_menu.config(bg=window_color, fg = "black")

        # create start button
        start_button = Button (self.start_window, text="Start", command=self.start_quiz)
        start_button.pack()

        quit_button = Button (self.start_window,text="Quit", command=sys.exit)
        quit_button.pack()

    # Create the question answer window for students
    def question_practice(self):
            
        self.question_ui.deiconify()  # show the hidden window
        self.question_ui.title("Propositional Logic Quizzer Practice")
        self.question_ui.configure(bg=window_color)
        center_window(self.question_ui, window_width, window_height)

        self.question_content_label = BlueLabel(self.question_ui, text="", bg=window_color)
        self.question_content_label.pack()

        if self.required_type == "Satisfiability": #creates two buttons for satisfiability
            satisfiable_button = radioButton(self.question_ui, text="Satisfiable", variable=self.satisfiability_var, value="sat").pack()
            unsatisfiable_button = radioButton(self.question_ui, text="Unsatisfiable", variable=self.satisfiability_var, value="unsat").pack()

        elif self.required_type == "Validity": #creates two buttons for validity
            valid_button = radioButton(self.question_ui, text="Valid", variable=self.validity_var, value="val").pack()
            invalid_button = radioButton(self.question_ui, text="Invalid", variable=self.validity_var, value="inval").pack()

        # elif self.required_type == "Truth Table":
        #     self.generate_truth_table()

        elif self.required_type == "DNF Form":
            self.answer_entry = tk.Text(self.question_ui, width=30, height=12, font=("Helvetica", 16))
            self.answer_entry.pack()
            self.answer_entry.bind("<FocusIn>", self.answer_entry_focus)
            self.add_connectives()
        
        else:
            self.table_entry = BlueLabel(self.question_ui, text = "", font=("Courier New", 15))
            self.table_entry.pack()
            self.table_answer = tk.Entry(self.question_ui, font=("Courier New", 15), bg=window_color, fg = "black")
            self.table_answer.pack()

        if self.required_type == "DNF Form":
            self.submit_button = Button (self.question_ui, text="Submit", command=self.check_logical_expression)
            self.submit_button.pack()
        
        elif self.required_type == "Truth Table":
            submit_button = Button (self.question_ui, text="Submit", command=self.check_table_input)
            submit_button.pack()

        else:
            submit_button = Button (self.question_ui, text="Submit", command=self.check_answer)
            submit_button.pack()

        self.status_label = BlueLabel(self.question_ui, text="")
        self.status_label.pack()

        next_button = Button (self.question_ui, text="Next", command=self.answer_next_question)
        next_button.pack()

    def check_logical_expression(self): #checks if the user input is a logical expression before checking answer
        expression = self.answer_entry.get("1.0", "end - 1 chars")
        if self.is_logical_expression(expression):
            self.check_answer()
            if self.invalid_input is not None:
                self.invalid_input.destroy()  # remove the label if it exists
        else:
            if self.invalid_input is None:
                self.invalid_input = BlueLabel(self.question_ui, text="Please enter a valid logical expression and re-submit")
            else:
                self.invalid_input.config(text="Please enter a valid logical expression")

    def check_table_input(self): #checks if the user input is 0 or 1 only
        expression = self.table_answer.get()
        if not re.match(r'^[01, ]*$', expression):
        # Display a widget to show an error message
            if self.table_error is None:
                self.table_error = BlueLabel(self.question_ui, text="Please enter only 0's and 1's")
                self.table_error.pack()
        else:
            self.check_answer()
            if self.table_error is not None:
                self.table_error.destroy()  # remove the label if it exists

    def question_test(self):
        self.question_ui.deiconify()  # show the hidden window
        self.question_ui.title("Propositional Logic Quizzer Test")
        self.question_ui.configure(bg=window_color)
        center_window(self.question_ui, window_width, window_height)

        self.question_content_label = BlueLabel(self.question_ui, text="", bg=window_color)
        self.question_content_label.pack()

        if self.required_type == "Satisfiability": #creates two buttons for satisfiability
            self.satisfiable_button = radioButton(self.question_ui, text="Satisfiable", variable=self.satisfiability_var, value="sat").pack()
            self.unsatisfiable_button = radioButton(self.question_ui, text="Unsatisfiable", variable=self.satisfiability_var, value="unsat").pack()

        elif self.required_type == "Validity": #creates two buttons for validity
            self.valid_button = radioButton(self.question_ui, text="Valid", variable=self.validity_var, value="val").pack()
            self.invalid_button = radioButton(self.question_ui, text="Unsatisfiable", variable=self.validity_var, value="inval").pack()

        elif self.required_type == "DNF Form":
            self.answer_entry = tk.Text(self.question_ui, width=30, height=12, font=("Helvetica", 16))
            self.answer_entry.pack()
            if self.required_type == "DNF Form":
                self.answer_entry.bind("<FocusIn>", self.answer_entry_focus)
                self.add_connectives()

        else:
            self.table_entry = BlueLabel(self.question_ui, text = "", font=("Courier New", 15))
            self.table_entry.pack()
            self.table_answer = tk.Entry(self.question_ui, font=("Courier New", 15), bg=window_color, fg = "black")
            self.table_answer.pack()

        select_time_label = BlueLabel(self.question_ui, text="Remaining time:")
        select_time_label.pack()

        self.remaining_time_var = tk.StringVar()
        self.timer = BlueLabel(self.question_ui, textvariable=self.remaining_time_var)
        self.timer.pack()

        self.status_label = BlueLabel(self.question_ui, text="")
        self.status_label.pack()

        if self.current_question_index != self.num_of_question:
            test_next_button = Button (self.question_ui, text="Next",
                                            command=lambda: [self.check_answer(), self.answer_next_question()])
            test_next_button.pack(padx = (0,25), side="right")

    def set_content_focus(self, event):
        self.content_focused = True
        self.formula_focused = False
        self.answer_focused = False

    def set_formula_focus(self, event):
        self.content_focused = False
        self.formula_focused = True
        self.answer_focused = False

    def answer_entry_focus(self, event):
        self.content_focused = False
        self.formula_focused = False
        self.answer_focused = True

    def add_connectives(self): #create buttons for user to easily access connectives

        def add_imply():
            if self.answer_focused == True:
                self.answer_entry.insert(tk.END, " -> ")
            elif self.formula_focused == True:
                self.formula_entry.insert(tk.END, " -> ")
            else:
                self.content_entry.insert(tk.END, " -> ")

        def add_or():
            if self.answer_focused == True:
                self.answer_entry.insert(tk.END, " \/ ")
            elif self.formula_focused == True:
                self.formula_entry.insert(tk.END, " \/ ")
            else:
                self.content_entry.insert(tk.END, " \/ ")
        def add_and():
            if self.answer_focused == True:
                self.answer_entry.insert(tk.END, " /\\ ")
            elif self.formula_focused == True:
                self.formula_entry.insert(tk.END, " /\\ ")
            else:
                self.content_entry.insert(tk.END, " /\\ ")
        def add_not():
            if self.answer_focused == True:
                self.answer_entry.insert(tk.END, " ~ ")
            elif self.formula_focused == True:
                self.formula_entry.insert(tk.END, " ~ ")
            else:
                self.content_entry.insert(tk.END, " ~ ")
        # def add_iff():
        #     if self.answer_focused == True:
        #         self.answer_entry.insert(tk.END, " <=> ")
        #     elif self.formula_focused == True:
        #         self.formula_entry.insert(tk.END, " <=> ")
        #     else:
        #         self.content_entry.insert(tk.END, " <=> ")
    
        self.imply_button = Button (self.question_ui, text="-->", command=add_imply).pack()
        self.or_button = Button (self.question_ui, text="\/", command=add_or).pack()
        self.and_button = Button (self.question_ui, text="/\\", command=add_and).pack()
        self.not_button = Button (self.question_ui, text="~", command=add_not).pack()
        # self.iff_button = Button (self.question_ui, text="<==>", command=add_iff).pack()

    def test_result_window(self):
        self.question_ui.title("Propositional Logic Quizzer Test Result")
        center_window(self.question_ui, window_width, window_height)
        self.question_ui.configure(bg=window_color)

        result = ""
        if len(self.test_result) == 0:
            question_mark_label = BlueLabel(self.question_ui, text="You answered all the questions correctly! Well done!")
            question_mark_label.pack()
        else:
            print(len(self.test_result))
            print(len(self.questions.keys()))
            rate = (1 - len(self.test_result) / len(self.questions.keys())) * 100
            question_mark_label = BlueLabel(self.question_ui, text="Mark: %.2f\n" % rate, font=("Courier New",25))
            question_mark_label.pack()

            for record in self.test_result:
                result += "Question No. {} \nQuestion content: {}\nYour answer: \n {}\nCorrect answer:\n{}\n".format(
                    record[0], record[1][1] + " " + record[1][2], record[2], record[3])
            result_label = BlueLabel(self.question_ui, text=result, font=("Courier New",15))
            result_label.pack()
        back_home_button = Button (self.question_ui, text="Back to Home page",command=self.back_home)
        back_home_button.pack()

    # Create the question append window for teachers
    def question_appender(self):
        self.question_ui.deiconify()
        self.question_ui.title("Propositional Logic Quizzer")
        center_window(self.question_ui, window_width, window_height)
        self.question_ui.configure(bg=window_color)
        # self.question_var = tk.StringVar()
        # self.formula_var = tk.StringVar()

        question_content_prompt = BlueLabel(self.question_ui, text="Enter question content: ")
        question_content_prompt.pack()

        self.content_entry = tk.Text(self.question_ui, width=30, height=10, font=("Helvetica", 16))
        self.content_entry.pack()
        self.content_entry.bind("<FocusIn>", self.set_content_focus)

        question_formula_prompt = BlueLabel(self.question_ui, text="Enter question formula: ")
        question_formula_prompt.pack()

        # formula_entry = tk.Entry(self.question_ui, textvariable=self.formula_var)
        # formula_entry.pack()

        self.formula_entry = tk.Text(self.question_ui, width=30, height=5, font=("Helvetica", 16))
        self.formula_entry.pack()
        self.formula_entry.bind("<FocusIn>", self.set_formula_focus)

        self.add_connectives()

        submit_button = Button (self.question_ui, text="Submit",
                                  command=lambda: self.write_question(question_file_name))
        submit_button.pack()

        self.submit_label = BlueLabel(self.question_ui, text="")
        self.submit_label.pack(pady=(0,10))

        next_button = Button (self.question_ui, text="Next", command=self.append_next_question)
        next_button.pack()

        back_home_button = Button (self.question_ui, text="Back to Home page", command=self.back_home)
        back_home_button.pack()

    # Append question into file
    def write_question(self, filename):
        formula = self.formula_entry.get("1.0", "end - 1 chars")
        formula = formula.replace("\\/", "|").replace("/\\", "&").replace("->", ">>").replace(" ", "")
        question_tuple = [self.required_type, self.content_entry.get("1.0", "end - 1 chars"), formula]
        contain_empty = False
        for item in question_tuple:
            if item == "":
                contain_empty = True
        print(question_tuple)
        if contain_empty:
            self.submit_label.config(text="Please enter both fields")
        elif self.is_logical_expression(formula) == False:
            self.submit_label.config(text="Please enter a valid expression")
        else:
            with open(filename, "a") as f:
                for items in question_tuple:
                    f.write(items + '\n')
            self.submit_label.config(text="Success")

    # Renew question append window
    def append_next_question(self):
        # self.question_var = ""
        # self.formula_var = ""
        self.content_entry.delete("1.0", "end - 1 chars")
        self.formula_entry.delete("1.0", "end - 1 chars")

    # Back to the start page
    def back_home(self):
        self.current_question_index = 0
        self.test_result = []
        self.question_ui.destroy()
        self.start_window.deiconify()

    def show_test_result(self):
        self.question_ui.destroy()
        self.question_ui = tk.Tk()
        self.test_result_window()

    # read question from the file
    def load_questions(self, filename):
        self.questions = {}
        with open(filename, "r") as f:
            index = 0
            question_tuple = []
            for line in f:
                line = line.strip()
                if not line:
                    continue
                question_tuple.append(line)
                if index % 3 == 2:
                    if question_tuple[0] == self.required_type:  # ensure the type is correct
                        self.questions[index // 3] = question_tuple  # [0] : type, [1]: question, [2]: formula
                    else:
                        index -= 3
                    question_tuple = []
                index += 1
        print(self.question_type_var.get())
        print(self.required_type)
        print(self.questions)

    # Renew question answer window
    def answer_next_question(self):
        if self.required_type == "DNF Form":
            self.answer_entry.delete("1.0", "end")
        if self.required_type == "Truth Table":
            self.table_answer.delete(0,"end")
        self.status_label.config(text="")
        if self.invalid_input is not None:
            self.invalid_input.destroy()
            self.invalid_input = None
        if self.table_error is not None :
            self.table_error.destroy()
            self.table_error = None
        if self.current_question_index < self.num_of_question:
            self.current_question = self.questions.get(list(self.questions.keys())[self.current_question_index])
            self.current_question_index += 1
            print(len(self.questions))
            print("index: ", self.current_question_index)
            print("current Q: ", self.current_question)
            self.question_content_label.config(text="Q{}/{}: {}".format(self.current_question_index,
                                                                        len(self.questions),
                                                                        self.current_question[1] + "\n" +
                                                                        self.current_question[2]).replace("|", "\\/").replace("&", "/\\").replace(">>", "->"))
            self.question_ui.update()
            print(self.current_question)
        else:
            if self.mode == practice:
                self.back_home()
                result = showwarning('Prompt', 'You have completed all the questions, please try other fields.')
                print(f'prompt: {result}')
            else:
                self.show_test_result()
        self.table_entry.config(text = "{}".format(self.empty_table(self.current_question[2])), compound = "top")
            

    def start_timer(self, time):
        for i in range(time, 0, -1):
            if self.current_question_index <= len(self.questions):
                self.remaining_time_var.set(i.__str__() + " s")
                self.question_ui.update()
                sleep(1)
        while self.current_question_index < len(self.questions):
            self.answer_next_question()
        self.show_test_result()

    def prompt_invalid(self, message):
        self.back_home()
        invalid = showwarning('Prompt', message)
        print(f'prompt: {invalid}')

    def shuffle_question(self):
        shuffled_dict = {}
        keys = list(self.questions.keys())
        random.shuffle(keys)
        for i in range(self.num_of_question):
            shuffled_dict[keys[i]] = self.questions.get(keys[i])
        self.questions = shuffled_dict
        print(self.questions)

    def switch_mode(self):
        if self.mode == append:
            if self.current_user_type == student:
                self.prompt_invalid("Student has no access to append question")
            else:
                self.question_appender()
        else:
            self.load_questions(question_file_name)
            if self.num_of_question > len(self.questions):
                self.prompt_invalid("No enough question")
            else:
                self.shuffle_question()
                if self.mode == practice:
                    self.question_practice()
                    self.answer_next_question()
                else:
                    remaining_time = self.num_of_question * TIME_EXPECTED_FOR_A_QUESTION
                    self.question_test()
                    self.answer_next_question()
                    self.start_timer(remaining_time)

    # Start our app
    def start_quiz(self):
        self.start_window.withdraw()
        self.question_ui = tk.Toplevel()
        self.current_user_type = self.user_type_var.get()
        self.required_type = self.question_type_var.get()
        self.mode = self.question_mode_var.get()
        self.num_of_question = int(self.num_question_var.get())
        self.switch_mode()
        print(self.current_question_index)
        print(self.current_user_type)

    # Check answer automatically
    def check_answer(self):
        if self.required_type == "Satisfiability":
            if self.satisfiability_var.get() == "sat":
                answer = "satisfiable"
            elif self.satisfiability_var.get() == "unsat":
                answer = "unsatisfiable"
            else:
                answer = "You must choose either one"
        elif self.required_type == "Validity":
            if self.validity_var.get() == "val":
                answer = "valid"
            elif self.validity_var.get() == "inval":
                answer = "invalid"
            else:
                answer = " "
                print("You must choose either one")
        elif self.required_type == "DNF Form":
            answer = self.answer_entry.get("1.0", "end - 1 chars")
            answer = answer.replace("\\/", "|").replace("/\\", "&").replace("->", ">>").replace(" ", "")
        else: #truth table entry
            answer = list(str(self.table_answer.get().replace(",", "").replace(" ", "")))

        answer_copy = answer
        is_dnf_form = True
        current_type = self.current_question[0]
        current_formula = self.current_question[2]
        solution = self.question_types[current_type]

        if current_type == "DNF Form" and answer != "":  # Special case if user did not enter simplest dnf
            if self.is_logical_expression(answer) == True:
                is_dnf_form = is_dnf(answer)
                answer = to_dnf(answer, True).__str__()
            elif current_type != "Truth Table":
                print(answer)
                self.check_logical_expression()
        
        if current_type != "Truth Table":
            solution(current_formula)
            answer = ''.join(answer.split())
            correct_copy = ''.join(self.correct_answer.split())
            print(answer.lower())
            print(correct_copy.lower())
        else:
            solution(current_formula)
            correct_copy = answer

        if current_type == "Truth Table":
            if answer == self.truth_table_values1:
                if self.mode == practice:
                    self.status_label.config(text="Correct")
            else:
                self.correct_answer = self.generate_table(current_formula)
                if self.mode == practice:
                    self.status_label.config(text="Incorrect\n" + "Suggested answer: \n" + self.correct_answer, font=("Courier New", 20))
                else:
                    self.test_result.append([self.current_question_index, self.current_question, answer_copy,
                                self.correct_answer])

        elif answer.lower() == correct_copy.lower() and is_dnf_form:
            if self.mode == practice:
                self.status_label.config(text="Correct")

        else:
            if self.mode == practice:
                self.status_label.config(text="Incorrect\n" + "Suggested answer: \n" + self.correct_answer)
            else:
                self.test_result.append([self.current_question_index, self.current_question, answer_copy,
                                    self.correct_answer])


    def is_logical_expression(self, expression):
        expression = expression.replace("\\/", "|").replace("/\\", "&").replace("->", ">>").replace(" ", "")
        # allowed symbols
        allowed_symbols = r">>|&~|\\|/"

        # check if string starts and ends with a letter
        if not expression[-1].isalpha():
            return False

        # check if two letters are directly next to each other
        if re.search(r"[A-Za-z]{2}", expression):
            return False

        # check if the string contains only allowed characters
        pattern = r"^[A-Za-z{}()]+(?<!>)$".format(allowed_symbols)
        if not re.match(pattern, expression):
            return False
        
        return True

    # Generate Truth table
    def show_truth_table(self, expression):
        self.correct_answer = ""
        self.propositions = regular.split(r'[^A-Za-z]', expression)  # remove connectives
        self.propositions = [item for item in self.propositions if item != '']  # remove empty propositions
        self.propositions = list(set(self.propositions))  # remove repeated propositions
        print(self.propositions)
        truth_table = sympy.logic.boolalg.truth_table(expression, self.propositions)
        self.truth_table_values1 = []
        self.truth_table_values2 = []

        for item in truth_table:
            self.correct_answer += "{0} -> {1}\n".format(*item)
            self.truth_table_values1.append(item[1]) #final column values
            self.truth_table_values2.append(item[0]) #values for each row
        #convert to strings for table generation
        self.truth_table_values2 = [[str(x) for x in inner_list] for inner_list in self.truth_table_values2]
        self.truth_table_values1 = [str(x) for x in self.truth_table_values1]
        if self.truth_table_values1[0] == 'True' or self.truth_table_values1[0] == 'False':
            self.truth_table_values1 = ["1" if x is "True" else "0" for x in self.truth_table_values1]



    def generate_table(self, expression):
        # Calculate the number of rows and columns
        num_rows = 2 ** len(self.propositions)
        num_cols = len(self.propositions) + 1
        expression = expression.replace("|", "\\/").replace("&", "/\\").replace(">>", "->")
        
        # Create a list to hold the header labels
        header_labels = []
        for i in self.propositions:
            header_labels.append(i)
        header_labels.append(expression)
        
        # Create a list of lists to hold the table cells
        table_cells = []
        for i in range(num_rows + 1):
            row_cells = []
            for j in range(num_cols):
                cell_text = ""
                if i == 0:
                    # This is a header cell, so use the header labels
                    cell_text = header_labels[j]
                else:
                    if j == num_cols - 1:
                        cell_text = self.truth_table_values1[i-1]
                    else:
                        cell_text = self.truth_table_values2[i-1][j]
                row_cells.append(cell_text)
            table_cells.append(row_cells)
        
        # Print the table as ASCII art
        table_str = ""
        col_width = max(len(label) for label in header_labels)
        for i in range(num_rows + 1):
            row_str = "|"
            for j in range(num_cols):
                row_str += " " + table_cells[i][j].ljust(col_width) + " |"
            table_str += row_str + "\n"
            if i == 0:
                table_str += "-" * len(row_str) + "\n"
        
        return table_str

        
    def empty_table(self,expression):
        # Calculate the number of rows and columns
        self.show_truth_table(expression)
        num_rows = 2 ** len(self.propositions)
        num_cols = len(self.propositions) + 1
        expression = expression.replace("|", "\\/").replace("&", "/\\").replace(">>", "->")

        # Create a list to hold the header labels
        header_labels = []
        for i in self.propositions:
            header_labels.append(i)
        header_labels.append(expression)

        # Create a list of lists to hold the table cells
        table_cells = []
        for i in range(num_rows + 1):
            row_cells = []
            for j in range(num_cols):
                cell_text = ""
                if i == 0:
                    # This is a header cell, so use the header labels
                    cell_text = header_labels[j]
                else:
                    if j == num_cols - 1:
                        cell_text = " "
                    else:
                        cell_text = self.truth_table_values2[i-1][j]
                row_cells.append(cell_text)
            table_cells.append(row_cells)

        # Print the table as ASCII art
        table_str = ""
        col_width = max(len(label) for label in header_labels)
        for i in range(num_rows + 1):
            row_str = "|"
            for j in range(num_cols):
                row_str += " " + table_cells[i][j].ljust(col_width) + " |"
            table_str += row_str + "\n"
            if i == 0:
                table_str += "-" * len(row_str) + "\n"

        return table_str

        # Generate Dnf expression
    # def convert_to_dnf(self, expression):
    #     dnf_expr = to_dnf(expression, True)
    #     self.correct_answer = dnf_expr.__str__()
    #
    # # Check the satisfiability
    # def check_satisfiability(self, expression):
    #     sympy_expr = parse_expr(expression)
    #     if satisfiable(sympy_expr):
    #         self.correct_answer = "Satisfiable"
    #     else:
    #         self.correct_answer = "Unsatisfiable"
    #
    # # Check the validity
    # def check_validity(self, expression):
    #     sympy_expr = parse_expr(expression)
    #     if valid(sympy_expr):
    #         self.correct_answer = "Valid"
    #     else:
    #         self.correct_answer = "Invalid"

        # Generate Dnf expression
    def convert_to_dnf(self, expression):
        dnf_expr = to_dnf(expression, True)
        self.correct_answer = dnf_expr.__str__()

    # Check the satisfiability
    def check_satisfiability(self, expression):
        sympy_expr = parse_expr(expression)
        if satisfiable(sympy_expr):
            self.correct_answer = "Satisfiable"
        else:
            self.correct_answer = "Unsatisfiable"

    # Check the validity
    def check_validity(self, expression):
        sympy_expr = parse_expr(expression)
        if valid(sympy_expr):
            self.correct_answer = "Valid"
        else:
            self.correct_answer = "Invalid"

# main
if __name__ == "__main__":
    root = tk.Tk()
    window_width = 800
    window_height = 800
    window_size = "{}x{}".format(window_width, window_height)
    app = LogicQuizzer(root)
    app.start()
    root.mainloop()