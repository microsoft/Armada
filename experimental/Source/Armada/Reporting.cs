// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Starmada {
  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Parser, Resolver 
  }

  public struct ErrorMessage {
    public Token token;
    public string message;
    public MessageSource source;
  }

  public abstract class ErrorReporter {
    public bool ErrorsOnly { get; set; }

    public bool HasErrors => ErrorCount > 0;
    public int ErrorCount => Count(ErrorLevel.Error);


    public abstract bool Message(MessageSource source, ErrorLevel level, Token tok, string msg);

    public void Error(MessageSource source, Token tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Error, tok, msg);
    }

    public abstract int Count(ErrorLevel level);

    // This method required by the Parser
    internal void Error(MessageSource source, string filename, int line, int col, string msg) {
      var tok = new Token();
      tok.line = line;
      tok.col = col;
      Error(source, tok, msg);
    }

    public void Error(MessageSource source, Token tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, s.FirstTok, msg, args);
    }

    public void Error(MessageSource source, Expr e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, e.FirstTok, msg, args);
    }

    public void Warning(MessageSource source, Token tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Warning, tok, msg);
    }

    public void Warning(MessageSource source, int line, int col, string msg) {
        Contract.Requires(msg != null);
        Token tok = new Token();
        tok.line = line;
        tok.col = col;
        Message(source, ErrorLevel.Warning, tok, msg);
    }

    public void Warning(MessageSource source, Token tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Warning(source, tok, String.Format(msg, args));
    }

    public void Info(MessageSource source, Token tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Info, tok, msg);
    }

    public void Info(MessageSource source, Token tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Info(source, tok, String.Format(msg, args));
    }

    public static string ErrorToString(ErrorLevel header, Token tok, string msg) {
      return String.Format("{0}: {1}{2}", TokenToString(tok), header.ToString(), ": " + msg);
    }

    public static string TokenToString(Token tok) {
      return String.Format("{0}({1},{2})", tok.val, tok.line, tok.col - 1);
    }
  }

  public abstract class BatchErrorReporter : ErrorReporter {
    private readonly Dictionary<ErrorLevel, List<ErrorMessage>> allMessages;

    protected BatchErrorReporter() {
      ErrorsOnly = false;
      allMessages = new Dictionary<ErrorLevel, List<ErrorMessage>> {
        [ErrorLevel.Error] = new(),
        [ErrorLevel.Warning] = new(),
        [ErrorLevel.Info] = new()
      };
    }

    public override bool Message(MessageSource source, ErrorLevel level, Token tok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        // discard the message
        return false;
      }
      allMessages[level].Add(new ErrorMessage { token = tok, message = msg });
      return true;
    }

    public override int Count(ErrorLevel level) {
      return allMessages[level].Count;
    }
  }

  public class ConsoleErrorReporter : BatchErrorReporter {
    private ConsoleColor ColorForLevel(ErrorLevel level) {
      switch (level) {
        case ErrorLevel.Error:
          return ConsoleColor.Red;
        case ErrorLevel.Warning:
          return ConsoleColor.Yellow;
        case ErrorLevel.Info:
          return ConsoleColor.Green;
        default:
          throw new Exception();
      }
    }

    public override bool Message(MessageSource source, ErrorLevel level, Token tok, string msg) {
      if (base.Message(source, level, tok, msg) && level != ErrorLevel.Info) {
        // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
        msg = msg.Replace(Environment.NewLine, Environment.NewLine + " ");

        ConsoleColor previousColor = Console.ForegroundColor;
        Console.ForegroundColor = ColorForLevel(level);
        var errorLine = ErrorToString(level, tok, msg);
        Console.WriteLine(errorLine);

        Console.ForegroundColor = previousColor;
        return true;
      } else {
        return false;
      }
    }
  }

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink() { }

    public override bool Message(MessageSource source, ErrorLevel level, Token tok, string msg) {
      return false;
    }

    public override int Count(ErrorLevel level) {
      return 0;
    }
  }

  public class ErrorReporterWrapper : BatchErrorReporter {

    private string msgPrefix;
    public readonly ErrorReporter WrappedReporter;

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    public override bool Message(MessageSource source, ErrorLevel level, Token tok, string msg) {
      base.Message(source, level, tok, msg);
      return WrappedReporter.Message(source, level, tok, msgPrefix + msg);
    }
  }
}