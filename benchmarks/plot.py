#!/usr/bin/env python3

import os, os.path, sys, argparse
import plotly.graph_objects as go
import pandas as pd
import plotly.io as pio
pio.kaleido.scope.mathjax = None

def valid_result(r):
    return r in {'sat', 'unsat'}

def read_csv_files(tools, csv_files, timeout):
    """
    Reads the CSV files and returns a dictionary with the tools as keys
    and their corresponding data as values.
    """
    data = {}
    for tool, csv_file in zip(tools, csv_files):
        if not os.path.exists(csv_file):
            print(f"Warning: {csv_file} does not exist. Skipping {tool}.")
            continue
        df = pd.read_csv(csv_file)
        df.loc[(df["Time (s)"] == -1) | (~ df["Result"].map(valid_result)), "Time (s)"] = timeout
        data[tool] = df
    return data

def make_survival_line(tool, data):
    """
    Creates a survival line for the given tool and its data.
    """
    # Sort the data by time
    data = data.sort_values(by="Time (s)", ascending=True, ignore_index=True)

    # Create the line
    return go.Scatter(
        x=data["Time (s)"],
        y=data.index,
        mode='lines+markers',
        name=tool
    ) 


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('tools',
                        default='_error_',
                        help='Comma-separated tool names.')
    parser.add_argument('tool_csvs',
                        default='_error_',
                        help='List of comma-separated CSV files containing tool data.')
    parser.add_argument('timeout', type=int,
                        default=-1,
                        help='Time value for the timeout.')
    parser.add_argument('-o', '--output', dest='output', 
                        default='output',
                        help='Name of the output file')
    args = parser.parse_args()
    
    if args.tools == '_error_':
        sys.exit('Please specify the tool names.')
    if args.tool_csvs == '_error_':
        sys.exit('Please specify paths to the CSV files.')
    if args.timeout < 0:
        sys.exit('Please specify a positive timeout value.')

    tools = args.tools.strip().split(",")
    tool_csvs = args.tool_csvs.strip().split(",")
    if len(tools) != len(tool_csvs):
        sys.exit("Error: different numbers of tools and CSV file were entered.")

    data = read_csv_files(tools, tool_csvs, args.timeout)

    # Create the Plotly object for Figure
    fig = go.Figure()

    for tool in tools:
        line = make_survival_line(tool, data[tool])
        fig.add_trace(line)

    # set the labels
    fig.update_layout(
        xaxis_title="Time (s)",
        yaxis_title="Number of benchmarks solved",
        xaxis_type="log",  # Set x-axis to logarithmic scale
        margin=dict(l=0, r=0, t=0, b=0)
    )

    fig.write_image(args.output+".survival.pdf", format='pdf')
