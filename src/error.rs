use ariadne::{Color, Label, Report, ReportKind};

use crate::lex::Span;

// message, reason, pos
#[derive(Debug)]
pub struct GenericError(pub String, pub String, pub Span);

impl GenericError {
    pub fn report(&self) -> Report<'static, std::ops::Range<usize>> {
        Report::build(ReportKind::Error, (), self.2.start)
            .with_message(self.0.clone())
            .with_label(
                Label::new(self.2.into_range())
                    .with_message(self.1.clone())
                    .with_color(Color::Red),
            )
            .finish()
    }
}
