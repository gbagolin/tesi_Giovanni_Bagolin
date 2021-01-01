import React, { useState } from 'react';

function NavBar() {
    return (
        <header>
            <nav className="navbar border">
                <ul className="nav">
                    <li className="nav-item">
                        <h3>Explainable Ai</h3>
                    </li>
                </ul>
                <span className="navbar-text">
                    <a href="">GitHub</a>
                </span>
            </nav>
        </header>
    )
}

export default NavBar;