# Written by Stephen Chen at 2023.02.25
import sys
import tkinter as tk
from tkinter.messagebox import *
import re as regular  # no idea there seems to have another re.py
from sympy.parsing.sympy_parser import parse_expr
import sympy.abc
import sympy
from sympy.logic.boolalg import to_dnf, is_dnf
from sympy.logic.inference import satisfiable, valid

window_size = "800x600"
window_width = 800
window_height = 600


# put the window to the center of screen
def center_window(window, w, h):
    ws = root.winfo_screenwidth()
    hs = root.winfo_screenheight()
    # calculate x, y positions
    x = (ws / 2) - (w / 2)
    y = (hs / 2) - (h / 2)
    window.geometry('%dx%d+%d+%d' % (w, h, x, y))


class LogicQuizzer:
    def __init__(self, root):
        # Global
        self.start_window = root  # window for start window
        self.question_ui = None  # window for question and answer also for appending question
        self.question_type_var = None  # question type been selected
        self.current_user_type = None  # String; store current user type
        self.user_type_var = None  # tk.Stringvar(); used to store usr typing for their type
        self.user_types = ["Teacher", "Student"]
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
        # self.answer_var = None  # String var to store user typing
        self.answer_entry = None  # tk.text to enable multiple lines entry
        self.correct_answer = None  # correct answer
        self.questions = {}  # all the question
        self.current_question = None  # current question tuple([0]: type, [1]: content, [2]: formula)
        self.current_question_index = 0  # current question index

        # Teacher window
        self.submit_label = None  # Question written into file successfully or not
        # self.formula_var = None  # Store formula user typed in
        # self.question_var = None  # Store question content user typed in
        self.formula_entry = None  # Store formula user typed in
        self.content_entry = None  # Store question content user typed in

    # Create start window
    def start(self):
        self.start_window.title("Propositional Logic Quizzer")
        center_window(self.start_window, window_width, window_height)

        select_type_label = tk.Label(self.start_window, text="Who are you:")
        select_type_label.pack()

        self.user_type_var = tk.StringVar()
        self.user_type_var.set(self.user_types[0])

        user_type_manu = tk.OptionMenu(self.start_window, self.user_type_var, *self.user_types)
        user_type_manu.pack()

        select_type_label = tk.Label(self.start_window, text="Select question type:")
        select_type_label.pack()

        self.question_type_var = tk.StringVar()
        self.question_type_var.set(list(self.question_types.keys())[0])

        question_type_menu = tk.OptionMenu(self.start_window, self.question_type_var, *self.question_types.keys())
        question_type_menu.pack()

        # create start button
        start_button = tk.Button(self.start_window, text="Start", command=self.start_quiz)
        start_button.pack()

        quit_button = tk.Button(self.start_window, text="Quit", command=sys.exit)
        quit_button.pack()

    # Create the question answer window for students
    def question_answer(self):
        self.question_ui.deiconify()  # show the hidden window
        self.question_ui.title("Propositional Logic Quizzer")
        center_window(self.question_ui, window_width, window_height)
        # self.answer_var = tk.StringVar()

        self.question_content_label = tk.Label(self.question_ui, text="")
        self.question_content_label.pack()

        # answer_entry = tk.Entry(self.question_ui, textvariable=self.answer_var)
        # answer_entry.pack()

        self.answer_entry = tk.Text(self.question_ui, width=30, height=12, font=("Helvetica", 16))
        self.answer_entry.pack()

        submit_button = tk.Button(self.question_ui, text="Submit", command=self.check_answer)
        submit_button.pack()

        self.status_label = tk.Label(self.question_ui, text="")
        self.status_label.pack()

        next_button = tk.Button(self.question_ui, text="Next", command=self.answer_next_question)
        next_button.pack()

    # Create the question append window for teachers
    def question_appender(self):
        self.question_ui.deiconify()
        self.question_ui.title("Propositional Logic Quizzer")
        center_window(self.question_ui, window_width, window_height)
        # self.question_var = tk.StringVar()
        # self.formula_var = tk.StringVar()

        question_content_prompt = tk.Label(self.question_ui, text="Enter question content: ")
        question_content_prompt.pack()

        self.content_entry = tk.Text(self.question_ui, width=30, height=10, font=("Helvetica", 16))
        self.content_entry.pack()

        question_formula_prompt = tk.Label(self.question_ui, text="Enter question formula: ")
        question_formula_prompt.pack()

        # formula_entry = tk.Entry(self.question_ui, textvariable=self.formula_var)
        # formula_entry.pack()

        self.formula_entry = tk.Text(self.question_ui, width=30, height=5, font=("Helvetica", 16))
        self.formula_entry.pack()

        submit_button = tk.Button(self.question_ui, text="Submit",
                                  command=lambda: self.write_question("questions.txt"))
        submit_button.pack()

        self.submit_label = tk.Label(self.question_ui, text="")
        self.submit_label.pack()

        next_button = tk.Button(self.question_ui, text="Next", command=self.append_next_question)
        next_button.pack()

        back_home_button = tk.Button(self.question_ui, text="Back to Home page", command=self.back_home)
        back_home_button.pack()

    # Append question into file
    def write_question(self, filename):
        question_tuple = [self.required_type, self.content_entry.get("1.0", "end - 1 chars"),
                          self.formula_entry.get("1.0", "end - 1 chars")]
        contain_empty = False
        for item in question_tuple:
            if item == "":
                contain_empty = True
        print(question_tuple)
        if not contain_empty:
            with open(filename, "a") as f:
                for items in question_tuple:
                    f.write(items + '\n')
            self.submit_label.config(text="Success")
        else:
            self.submit_label.config(text="Wops! Something went wrong")

    # Renew question append window
    def append_next_question(self):
        # self.question_var = ""
        # self.formula_var = ""
        self.content_entry.delete("1.0", "end - 1 chars")
        self.formula_entry.delete("1.0", "end - 1 chars")

    # Back to the start page
    def back_home(self):
        self.current_question_index = 0
        self.question_ui.destroy()
        self.start_window.deiconify()

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
        self.answer_entry.delete("1.0", "end")
        self.status_label.config(text="")
        if self.current_question_index < len(self.questions):
            self.current_question = self.questions.get(self.current_question_index)
            print(len(self.questions))
            print("index: ", self.current_question_index)
            print("current Q: ", self.current_question)
            self.question_content_label.config(text=self.current_question[1] + "\n" + self.current_question[2])
            print(self.current_question)
            self.current_question_index += 1
        else:
            self.back_home()
            result = showwarning('Prompt', 'You have completed all the questions, please try other fields.')
            print(f'prompt: {result}')

    # Start our app
    def start_quiz(self):
        self.start_window.withdraw()
        self.question_ui = tk.Toplevel()
        self.current_user_type = self.user_type_var.get()
        self.required_type = self.question_type_var.get()
        if self.current_user_type == "Student":
            self.question_answer()
            self.load_questions("questions.txt")
            self.answer_next_question()
            print(self.current_question_index)
            print(self.current_user_type)
        else:
            self.question_appender()

    # Check answer automatically
    def check_answer(self):
        # answer = self.answer_var.get()
        answer = self.answer_entry.get("1.0", "end - 1 chars")
        is_dnf_form = True
        current_type = self.current_question[0]
        current_formula = self.current_question[2]
        solution = self.question_types[current_type]

        if current_type == "DNF Form" and answer != "":  # Special case if user did not enter simplest dnf
            is_dnf_form = is_dnf(answer)
            answer = to_dnf(answer, True).__str__()
        answer = ''.join(answer.split())

        solution(current_formula)
        correct_copy = ''.join(self.correct_answer.split())
        print(answer.lower())
        print(correct_copy.lower())
        if answer.lower().lower() == correct_copy.lower() and is_dnf_form:
            self.status_label.config(text="Correct")
        else:
            self.status_label.config(text="Incorrect\n" + "Suggested answer: \n" + self.correct_answer)

    # Generate Truth table
    def show_truth_table(self, expression):
        self.correct_answer = ""
        propositions = regular.split(r'[^A-Za-z]', expression)  # remove connectives
        propositions = [item for item in propositions if item != '']  # remove empty propositions
        propositions = list(set(propositions))  # remove repeated propositions
        truth_table = sympy.logic.boolalg.truth_table(expression, propositions)
        for item in truth_table:
            self.correct_answer += "{0} -> {1}\n".format(*item)
        print(self.correct_answer)

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
    app = LogicQuizzer(root)
    app.start()
    root.mainloop()
